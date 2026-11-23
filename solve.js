// Fast drop-in for makefun-site 1.0.0 — tuned v3 (tuning round 3).
//
// Same answers, byte for byte, for every input — reimplemented here from the
// published semantics (front matter, template dialect, Markdown subset, slug
// rule, report) with the hot paths rebuilt for CPU time:
//
//  * Markdown is rendered in one fused pass over the lines (no token array,
//    no per-block object allocations); inline rendering uses ONE regex scan
//    for all nine special characters, so the plain runs between matches
//    contain no HTML special and need no escaping pass at all. A string
//    with no special at all is returned untouched (no output array).
//  * HTML escaping is a single regex exec loop (one native scan, no
//    replace callback), and returns the original string untouched when
//    nothing needs escaping.
//  * Template variable lookup takes a direct property load for the first
//    segment, falling back to the hasOwn scope walk only when undefined.
//  * Each page render hangs its vars off one shared per-case scope holding
//    site/tags/recent, instead of spreading those into a fresh object.
//  * The table of contents is passed through as-is: its entries already
//    have the output shape, so pageOf copies nothing.
//  * slugify takes an ASCII fast path (no NFKD / mark stripping when the
//    text is pure ASCII) and memoises every distinct string within one case
//    only — the cache is rebuilt for every run() call, never shared across
//    cases.
//  * Front matter is parsed by scanning line boundaries in the raw text
//    (no whole-file split, no per-line regexes); the body is a slice, not a
//    re-joined copy.
//  * Templates render into one shared output array (joined once per page)
//    with plain for-loops instead of forEach closures; each render builds
//    one fresh scope object instead of mutating and un-mutating a shared one.
//  * Relative links resolve by scanning the directory string, with no
//    split/join arrays; the scheme test is a hand scan, not a regex.
//  * Word counting, date words and slug uniqueness are hand scans.
//
// Nothing is cached from one case to the next. Deterministic, stdlib only.

const MONTHS = ['January', 'February', 'March', 'April', 'May', 'June', 'July', 'August', 'September', 'October', 'November', 'December'];
const RESERVED = ['posts', 'tags', 'page'];
const KEYS = new Set(['title', 'date', 'tags', 'draft', 'layout', 'slug', 'summary']);
const ESC = { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' };
// One regex, one native scan: the exec loop below pushes the plain runs
// between matches and the entity for each match, so a string with specials
// is scanned once (the old test()+replace() scanned it twice, and the
// replace callback ran per match).
const ESC_RE = /[&<>"']/g;

// Whitespace code units, by the same set wordsOf used: JS \s.
const WS = new Uint8Array(65536);
for (const c of [9, 10, 11, 12, 13, 32, 160, 5760, 8192, 8193, 8194, 8195, 8196, 8197, 8198, 8199, 8200, 8201, 8202, 8232, 8233, 8239, 8287, 12288, 65279]) WS[c] = 1;

// Characters a backslash may escape in inline Markdown.
const ESC_TBL = new Uint8Array(128);
for (const ch of '\\`*_[]()#+-.!>') ESC_TBL[ch.charCodeAt(0)] = 1;

const byCodeUnits = (a, b) => (a < b ? -1 : a > b ? 1 : 0);
const dirOf = (p) => { const i = p.lastIndexOf('/'); return i === -1 ? '' : p.slice(0, i); };

// Per-case slug cache: created fresh inside every run(), never reused.
let slugCache = null;

function esc(s) {
  ESC_RE.lastIndex = 0;
  let m = ESC_RE.exec(s);
  if (m === null) return s;
  const out = [];
  let i = 0;
  do {
    if (m.index > i) out.push(s.slice(i, m.index));
    out.push(ESC[m[0]]);
    i = m.index + 1;
  } while ((m = ESC_RE.exec(s)) !== null);
  if (i < s.length) out.push(s.slice(i));
  return out.join('');
}

function slugify(text) {
  const hit = slugCache.get(text);
  if (hit !== undefined) return hit;
  let plain = text;
  if (/[^\x00-\x7F]/.test(text)) plain = text.normalize('NFKD').replace(/\p{M}/gu, '');
  let out = '';
  let gap = false;
  for (let i = 0; i < plain.length; i++) {
    const ch = plain[i];
    let keep = null;
    if (ch >= 'A' && ch <= 'Z') keep = ch.toLowerCase();
    else if ((ch >= 'a' && ch <= 'z') || (ch >= '0' && ch <= '9')) keep = ch;
    if (keep === null) { gap = out.length > 0; continue; }
    if (gap) out += '-';
    gap = false;
    out += keep;
  }
  if (out.length > 64) out = out.slice(0, 64);
  let e = out.length;
  while (e > 0 && out[e - 1] === '-') e--;
  out = e === out.length ? out : out.slice(0, e);
  if (out === '') out = 'untitled';
  slugCache.set(text, out);
  return out;
}

function uniqueSlug(slug, taken) {
  let out = slug;
  for (let n = 2; taken.has(out); n++) out = slug + '-' + n;
  taken.add(out);
  return out;
}

function longDate(date) {
  return Number(date.slice(8, 10)) + ' ' + MONTHS[Number(date.slice(5, 7)) - 1] + ' ' + date.slice(0, 4);
}

// --------------------------------------------------------------- front matter

function daysIn(y, m) {
  if (m === 2) return (y % 4 === 0 && y % 100 !== 0) || y % 400 === 0 ? 29 : 28;
  return m === 4 || m === 6 || m === 9 || m === 11 ? 30 : 31;
}

function stringOf(raw) {
  if (raw[0] === '"') {
    if (raw.length < 2 || raw[raw.length - 1] !== '"') return { error: 'a quoted string is not closed' };
    let out = '';
    for (let i = 1; i < raw.length - 1; i++) {
      const c = raw[i];
      if (c === '\\') {
        const n = raw[i + 1];
        if ((n !== '"' && n !== '\\') || i + 1 === raw.length - 1) return { error: 'a quoted string holds an escape other than \\" or \\' };
        out += n;
        i++;
      } else if (c === '"') return { error: 'a quoted string holds a stray quote' };
      else out += c;
    }
    return { value: out };
  }
  if (raw[0] === '[') return { error: 'a bare string opens on [' };
  return { value: raw };
}

function valueOf(key, raw) {
  if (key === 'title' || key === 'summary') {
    const s = stringOf(raw);
    return 'error' in s ? { error: 'key "' + key + '": ' + s.error } : s;
  }
  if (key === 'date') {
    let ok = raw.length === 10 && raw[4] === '-' && raw[7] === '-';
    if (ok) for (let i = 0; i < 10; i++) {
      if (i === 4 || i === 7) continue;
      if (raw[i] < '0' || raw[i] > '9') { ok = false; break; }
    }
    const y = ok ? Number(raw.slice(0, 4)) : 0;
    const mo = ok ? Number(raw.slice(5, 7)) : 0;
    const d = ok ? Number(raw.slice(8, 10)) : 0;
    if (!ok || y < 1970 || y > 2099 || mo < 1 || mo > 12 || d < 1 || d > daysIn(y, mo))
      return { error: 'key "date": not a date from 1970-01-01 to 2099-12-31 (YYYY-MM-DD)' };
    return { value: raw };
  }
  if (key === 'tags') {
    if (raw[0] !== '[' || raw[raw.length - 1] !== ']') return { error: 'key "tags": not a list [a, b]' };
    const inner = raw.slice(1, -1);
    if (inner.trim() === '') return { value: [] };
    const tags = inner.split(',');
    for (let i = 0; i < tags.length; i++) {
      tags[i] = tags[i].trim();
      const t = tags[i];
      if (t === '') return { error: 'key "tags": an empty tag, or one holding " [ or ]' };
      for (let j = 0; j < t.length; j++) if (t[j] === '"' || t[j] === '[' || t[j] === ']')
        return { error: 'key "tags": an empty tag, or one holding " [ or ]' };
    }
    return { value: tags };
  }
  if (key === 'draft') {
    if (raw === 'true') return { value: true };
    if (raw === 'false') return { value: false };
    return { error: 'key "draft": true or false' };
  }
  if (key === 'layout') {
    let ok = raw.length > 0;
    if (ok) for (let i = 0; i < raw.length; i++) {
      const c = raw[i];
      if (!((c >= 'a' && c <= 'z') || (c >= '0' && c <= '9') || c === '-')) { ok = false; break; }
    }
    return ok ? { value: raw } : { error: 'key "layout": not a template name' };
  }
  if (key === 'slug') {
    let ok = raw.length > 0 && raw.length <= 64;
    if (ok) {
      // a-z0-9 groups joined by single '-'
      let prevDash = true;
      for (let i = 0; i < raw.length; i++) {
        const c = raw[i];
        if (c === '-') { if (prevDash) { ok = false; break; } prevDash = true; }
        else if ((c >= 'a' && c <= 'z') || (c >= '0' && c <= '9')) prevDash = false;
        else { ok = false; break; }
      }
      if (prevDash) ok = false;
    }
    return ok ? { value: raw } : { error: 'key "slug": not a slug' };
  }
  return { error: 'unknown key "' + key + '"' };
}

function isBlankLine(s) {
  for (let i = 0; i < s.length; i++) if (s[i] !== ' ' && s[i] !== '\t') return false;
  return true;
}

function trimST(s) {
  let e = s.length;
  while (e > 0 && (s[e - 1] === ' ' || s[e - 1] === '\t')) e--;
  return e === s.length ? s : s.slice(0, e);
}

function parseFrontMatter(text) {
  const firstNl = text.indexOf('\n');
  if (firstNl === -1) {
    if (text !== '---') return { error: 'no front matter' };
    return { error: 'the front matter is not closed' };
  }
  if (text.slice(0, firstNl) !== '---') return { error: 'no front matter' };
  const data = {};
  let start = firstNl + 1;
  let lineNo = 1; // 0-based index of the line being read; opening '---' is line 0
  for (;;) {
    const nl = text.indexOf('\n', start);
    const lineEnd = nl === -1 ? text.length : nl;
    const line = text.slice(start, lineEnd);
    if (line === '---') {
      if (!Object.hasOwn(data, 'title')) return { error: 'no title' };
      return { data, body: nl === -1 ? '' : text.slice(nl + 1) };
    }
    if (!isBlankLine(line) && line[0] !== '#') {
      let k = 0;
      while (k < line.length && ((line[k] >= 'a' && line[k] <= 'z') || line[k] === '_')) k++;
      if (k === 0 || k >= line.length || line[k] !== ':')
        return { error: 'line ' + (lineNo + 1) + ' is not "key: value"' };
      const key = line.slice(0, k);
      let raw;
      if (k + 1 === line.length) raw = '';
      else if (line[k + 1] === ' ') raw = line.slice(k + 2);
      else return { error: 'line ' + (lineNo + 1) + ' is not "key: value"' };
      raw = trimST(raw);
      if (!KEYS.has(key)) return { error: 'unknown key "' + key + '"' };
      if (Object.hasOwn(data, key)) return { error: 'key "' + key + '" is given twice' };
      if (raw === '') return { error: 'key "' + key + '" has no value' };
      const v = valueOf(key, raw);
      if ('error' in v) return v;
      data[key] = v.value;
    }
    if (nl === -1) return { error: 'the front matter is not closed' };
    start = nl + 1;
    lineNo++;
  }
}

// ------------------------------------------------------------------- markdown

function trimLine(line) {
  if (line.length === 0) return line;
  const first = line[0];
  const last = line[line.length - 1];
  if (first !== ' ' && first !== '\t' && last !== ' ' && last !== '\t') return line;
  let a = 0;
  let b = line.length;
  while (a < b && (line[a] === ' ' || line[a] === '\t')) a++;
  while (b > a && (line[b - 1] === ' ' || line[b - 1] === '\t')) b--;
  return line.slice(a, b);
}

function isLangChar(c) {
  return (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9') || c === '_' || c === '+' || c === '-';
}

// Language of a fence-open line, '' for a bare fence, null when not a fence.
function fenceLang(line) {
  if (line[0] !== '`' || line[1] !== '`' || line[2] !== '`') return null;
  let j = 3;
  while (j < line.length && isLangChar(line[j])) j++;
  for (let i = j; i < line.length; i++) if (line[i] !== ' ' && line[i] !== '\t') return null;
  return line.slice(3, j);
}

function isFenceClose(line) {
  if (line[0] !== '`' || line[1] !== '`' || line[2] !== '`') return false;
  for (let i = 3; i < line.length; i++) if (line[i] !== ' ' && line[i] !== '\t') return false;
  return true;
}

function headingOf(line) {
  let n = 0;
  while (line[n] === '#') n++;
  if (n < 1 || n > 6) return null;
  if (line[n] !== ' ' && line[n] !== '\t') return null;
  let j = n;
  while (line[j] === ' ' || line[j] === '\t') j++;
  let e = line.length;
  while (e > j && (line[e - 1] === ' ' || line[e - 1] === '\t')) e--;
  if (e === j) return null;
  return { depth: n, text: line.slice(j, e) };
}

function isHR(line) {
  const t = line[0] === '-' && line[1] === '-' && line[2] === '-' ? 3 : line[0] === '*' && line[1] === '*' && line[2] === '*' ? 3 : -1;
  if (t === -1) return false;
  for (let i = 3; i < line.length; i++) if (line[i] !== ' ' && line[i] !== '\t') return false;
  return true;
}

function endsParagraph(line) {
  if (line === '') return true;
  const c0 = line.charCodeAt(0);
  if (c0 === 32 || c0 === 9) return isBlankLine(line);
  if (c0 === 96) return fenceLang(line) !== null;
  if (c0 === 35) return headingOf(line) !== null;
  if (c0 === 45 || c0 === 42) return isHR(line);
  return false;
}

// A list-open line: {ordered, num, text} or null.
function listOpen(line) {
  if ((line[0] === '-' || line[0] === '*') && line[1] === ' ') return { ordered: false, num: 0, text: line.slice(2) };
  let j = 0;
  while (line[j] >= '0' && line[j] <= '9') j++;
  if (j >= 1 && j <= 9 && line[j] === '.' && line[j + 1] === ' ') return { ordered: true, num: line.slice(0, j), text: line.slice(j + 2) };
  return null;
}

// A following item line of the same list kind, or null.
function listItem(line, ordered) {
  if (!ordered) {
    if ((line[0] === '-' || line[0] === '*') && line[1] === ' ') return line.slice(2);
    return null;
  }
  let j = 0;
  while (line[j] >= '0' && line[j] <= '9') j++;
  if (j >= 1 && j <= 9 && line[j] === '.' && line[j + 1] === ' ') return line.slice(j + 2);
  return null;
}

function isContinued(line) {
  let j = 0;
  while (line[j] === ' ') j++;
  if (j < 2 || j >= line.length) return false;
  const c = line[j];
  return c !== ' ' && c !== '\t' && c !== '\n' && c !== '\r' && c !== '\v' && c !== '\f' && c !== '\u00a0';
}

function findUnescaped(s, what, from) {
  const wl = what.length;
  for (let j = from; j <= s.length - wl; j++) {
    if (s[j] === '\\' && j + 1 < s.length) { const c1 = s.charCodeAt(j + 1); if (c1 < 128 && ESC_TBL[c1]) { j++; continue; } }
    if (s.startsWith(what, j)) return j;
  }
  return -1;
}

function findSingleStar(s, from) {
  for (let j = from; j < s.length; j++) {
    const c = s[j];
    if (c === '\\' && j + 1 < s.length) { const c1 = s.charCodeAt(j + 1); if (c1 < 128 && ESC_TBL[c1]) { j++; continue; } }
    if (c !== '*') continue;
    if (s[j + 1] === '*') { j++; continue; }
    return j;
  }
  return -1;
}

// One scan for every character inline Markdown or HTML escaping cares
// about: \ ` * [ and & < > " '. The plain run between two matches holds
// none of them, so it is pushed as-is — no escaping pass over it.
// (The class is written [\\`*&<>"'[]: the '[' before the closing ']' is
// a literal member, so the class holds all nine characters.)
const ALL = /[\\`*&<>"'[]/g;

function inline(s, env) {
  // One scan for every character inline Markdown or HTML escaping cares
  // about: \ ` * [ and & < > " '. The plain run between two matches holds
  // none of them, so it is pushed as-is — no escaping pass over it.
  // (The class is written [\\`*&<>"'[]: the '[' before the closing ']' is
  // a literal member, so the class holds all nine characters.)
  // No special at all is the common paragraph: return the string itself
  // instead of allocating an output array and joining one element.
  ALL.lastIndex = 0;
  let m = ALL.exec(s);
  if (m === null) return s;
  const out = [];
  let i = 0;
  for (;;) {
    const j = m.index;
    if (j > i) out.push(s.slice(i, j));
    i = j;
    const c = s[i];
    if (c === '&' || c === '<' || c === '>' || c === '"' || c === "'") { out.push(ESC[c]); i++; }
    else if (c === '\\' && i + 1 < s.length) {
      const c1 = s.charCodeAt(i + 1);
      if (c1 < 128 && ESC_TBL[c1]) { out.push(ESC[s[i + 1]] || s[i + 1]); i += 2; }
      else { out.push('\\'); i++; }
    }
    else if (c === '`') {
      const k = s.indexOf('`', i + 1);
      if (k > i + 1) {
        out.push('<code>', esc(s.slice(i + 1, k)), '</code>');
        i = k + 1;
      } else { out.push('`'); i++; }
    }
    else if (c === '*') {
      if (s[i + 1] === '*') {
        const k = findUnescaped(s, '**', i + 2);
        if (k > i + 2) {
          out.push('<strong>', inline(s.slice(i + 2, k), env), '</strong>');
          i = k + 2;
        } else { out.push('**'); i += 2; }
      } else {
        const k = findSingleStar(s, i + 1);
        if (k > i + 1) {
          out.push('<em>', inline(s.slice(i + 1, k), env), '</em>');
          i = k + 1;
        } else { out.push('*'); i++; }
      }
    }
    else if (c === '[') {
      const k = findUnescaped(s, ']', i + 1);
      const mm = k !== -1 && s[k + 1] === '(' ? s.indexOf(')', k + 2) : -1;
      const target = mm === -1 ? '' : s.slice(k + 2, mm);
      if (target !== '' && !/\s/.test(target)) {
        out.push('<a href="', esc(env.link(target)), '">', inline(s.slice(i + 1, k), env), '</a>');
        i = mm + 1;
      } else { out.push('['); i++; }
    }
    else { out.push('\\'); i++; }
    if (i >= s.length) break;
    ALL.lastIndex = i;
    m = ALL.exec(s);
    if (m === null) { out.push(s.slice(i)); break; }
  }
  return out.join('');
}

function renderMarkdown(src, env) {
  // Split into lines and count the body's words in one pass over src:
  // a word is a run of non-whitespace code units, and a line break is
  // whitespace, so the per-line counts add up to the body's count.
  const lines = [];
  let words = 0;
  let inWord = false;
  let start = 0;
  for (let i = 0; i < src.length; i++) {
    const c = src.charCodeAt(i);
    if (c === 10) { lines.push(src.slice(start, i)); start = i + 1; inWord = false; }
    else if (WS[c]) inWord = false;
    else if (!inWord) { words++; inWord = true; }
  }
  lines.push(src.slice(start));
  const ids = new Set();
  const out = [];
  const toc = [];
  let excerpt = null;
  let i = 0;
  while (i < lines.length) {
    const line = lines[i];
    if (line === '') { i++; continue; }
    const c0 = line.charCodeAt(0);
    if (c0 === 32 || c0 === 9) {
      if (isBlankLine(line)) { i++; continue; }
      // otherwise a paragraph (fall through below)
    } else if (c0 === 96) {
      const lang = fenceLang(line);
      if (lang !== null) {
        i++;
        const body = [];
        while (i < lines.length && !isFenceClose(lines[i])) body.push(lines[i++]);
        i++;
        out.push('<pre><code' + (lang === '' ? '' : ' class="language-' + esc(lang) + '"') + '>');
        // esc() never touches '\n', so one escape over the joined body
        // is the same as escaping each line on its own.
        out.push(esc(body.length === 0 ? '' : body.join('\n') + '\n'));
        out.push('</code></pre>\n');
        continue;
      }
    } else if (c0 === 35) {
      const hd = headingOf(line);
      if (hd !== null) {
        const id = uniqueSlug(slugify(hd.text), ids);
        const html = inline(hd.text, env);
        out.push('<h' + hd.depth + ' id="' + id + '">' + html + '</h' + hd.depth + '>\n');
        if (hd.depth === 2 || hd.depth === 3) toc.push({ level: hd.depth, id, html });
        i++;
        continue;
      }
    } else if (c0 === 45 || c0 === 42) {
      if (isHR(line)) { out.push('<hr>\n'); i++; continue; }
      const lo = listOpen(line);
      if (lo !== null) {
        const items = [];
        const start = lo.ordered ? Number(lo.num) : 1;
        while (i < lines.length) {
          const m = listItem(lines[i], lo.ordered);
          if (m !== null) { items.push([trimLine(m)]); i++; }
          else if (isContinued(lines[i])) { items[items.length - 1].push(trimLine(lines[i])); i++; }
          else break;
        }
        const tag = lo.ordered ? 'ol' : 'ul';
        out.push(lo.ordered && start !== 1 ? '<ol start="' + start + '">\n' : '<' + tag + '>\n');
        for (const it of items) out.push('<li>' + inline(it.join('\n'), env) + '</li>\n');
        out.push('</' + tag + '>\n');
        continue;
      }
    } else if (c0 === 62) {
      const body = [];
      while (i < lines.length && lines[i][0] === '>') {
        const l = lines[i++];
        body.push(trimLine(l[1] === ' ' ? l.slice(2) : l.slice(1)));
      }
      const kept = [];
      for (const l of body) if (l !== '') kept.push(l);
      if (kept.length === 0) out.push('<blockquote>\n</blockquote>\n');
      else out.push('<blockquote>\n<p>' + inline(kept.join('\n'), env) + '</p>\n</blockquote>\n');
      continue;
    } else if (c0 >= 48 && c0 <= 57) {
      const lo = listOpen(line);
      if (lo !== null) {
        const items = [];
        const start = Number(lo.num);
        while (i < lines.length) {
          const m = listItem(lines[i], true);
          if (m !== null) { items.push([trimLine(m)]); i++; }
          else if (isContinued(lines[i])) { items[items.length - 1].push(trimLine(lines[i])); i++; }
          else break;
        }
        out.push(start !== 1 ? '<ol start="' + start + '">\n' : '<ol>\n');
        for (const it of items) out.push('<li>' + inline(it.join('\n'), env) + '</li>\n');
        out.push('</ol>\n');
        continue;
      }
    }
    const body = [trimLine(line)];
    i++;
    while (i < lines.length && !endsParagraph(lines[i])) body.push(trimLine(lines[i++]));
    const html = inline(body.join('\n'), env);
    if (excerpt === null) excerpt = html;
    out.push('<p>' + html + '</p>\n');
  }
  return { html: out.join(''), toc, excerpt: excerpt === null ? '' : excerpt, words };
}

// ------------------------------------------------------------------ templates

class TemplateError extends Error {}

const PATH_RE = /^[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*$/;
const FOR_RE = /^for ([A-Za-z_][A-Za-z0-9_]*) in (\S+)$/;
const IF_RE = /^if (not )?(\S+)$/;
const INCLUDE_RE = /^include "([a-z0-9-]+)"$/;

function pathOf(name, text) {
  if (!PATH_RE.test(text)) throw new TemplateError('template "' + name + '": ' + JSON.stringify(text) + ' is not a path');
  return text.split('.');
}

function tokenize(name, src) {
  const tokens = [];
  let text = '';
  let i = 0;
  while (i < src.length) {
    const open = src.indexOf('{', i);
    if (open === -1 || open === src.length - 1) { text += src.slice(i); break; }
    const next = src[open + 1];
    if (next !== '{' && next !== '%') { text += src.slice(i, open + 1); i = open + 1; continue; }
    text += src.slice(i, open);
    if (next === '{') {
      const raw = src[open + 2] === '{';
      const close = src.indexOf(raw ? '}}}' : '}}', open + (raw ? 3 : 2));
      if (close === -1) throw new TemplateError('template "' + name + '": a ' + (raw ? '{{{' : '{{') + ' is not closed');
      if (text !== '') tokens.push({ t: 'text', text });
      text = '';
      tokens.push({ t: raw ? 'raw' : 'var', path: pathOf(name, src.slice(open + (raw ? 3 : 2), close).trim()) });
      i = close + (raw ? 3 : 2);
      continue;
    }
    const close = src.indexOf('%}', open + 2);
    if (close === -1) throw new TemplateError('template "' + name + '": a {% is not closed');
    const end = close + 2;
    const lineStart = src.lastIndexOf('\n', open - 1) + 1;
    const nl = src.indexOf('\n', end);
    const lineEnd = nl === -1 ? src.length : nl;
    const standalone = isBlankLine(src.slice(lineStart, open)) && isBlankLine(src.slice(end, lineEnd));
    if (standalone) text = text.slice(0, text.length - (open - lineStart));
    if (text !== '') tokens.push({ t: 'text', text });
    text = '';
    tokens.push({ t: 'tag', tag: src.slice(open + 2, close).trim() });
    i = standalone ? (nl === -1 ? src.length : nl + 1) : end;
  }
  if (text !== '') tokens.push({ t: 'text', text });
  return tokens;
}

function parseTemplate(name, src) {
  const root = { kind: 'root', body: [] };
  const stack = [root];
  let body = root.body;
  for (const tok of tokenize(name, src)) {
    if (tok.t === 'text') body.push({ kind: 'text', text: tok.text });
    else if (tok.t === 'var' || tok.t === 'raw') body.push({ kind: tok.t, path: tok.path });
    else {
      const tag = tok.tag;
      const top = stack[stack.length - 1];
      let m;
      if ((m = FOR_RE.exec(tag)) !== null) {
        const node = { kind: 'for', name: m[1], path: pathOf(name, m[2]), body: [] };
        body.push(node);
        stack.push(node);
        body = node.body;
      } else if ((m = IF_RE.exec(tag)) !== null) {
        const node = { kind: 'if', not: m[1] !== undefined, path: pathOf(name, m[2]), then: [], else: null };
        body.push(node);
        stack.push(node);
        body = node.then;
      } else if (tag === 'else') {
        if (top.kind !== 'if' || top.else !== null) throw new TemplateError('template "' + name + '": an else outside an if');
        top.else = [];
        body = top.else;
      } else if (tag === 'endfor' || tag === 'endif') {
        if (top.kind !== (tag === 'endfor' ? 'for' : 'if')) throw new TemplateError('template "' + name + '": an ' + tag + ' with no open ' + tag.slice(3));
        stack.pop();
        const parent = stack[stack.length - 1];
        body = parent.kind === 'root' ? parent.body : parent.kind === 'for' ? parent.body : (parent.else !== null && parent.else !== undefined ? parent.else : parent.then);
      } else if ((m = INCLUDE_RE.exec(tag)) !== null) body.push({ kind: 'include', name: m[1] });
      else throw new TemplateError('template "' + name + '": {% ' + tag + ' %} is not a tag');
    }
  }
  if (stack.length > 1) throw new TemplateError('template "' + name + '": a ' + stack[stack.length - 1].kind + ' is not closed');
  return root.body;
}

function lookup(scope, path) {
  // Fast path: the first segment almost always lives in the innermost
  // scope, so one property load finds it. Only when that load is
  // undefined do the hasOwn walk — which also covers a scope that holds
  // the key with an undefined value, and a key that lives in a parent.
  let v = scope.vars[path[0]];
  if (v === undefined) {
    let s = scope;
    while (s !== null && !Object.hasOwn(s.vars, path[0])) s = s.parent;
    if (s === null) return undefined;
    v = s.vars[path[0]];
  }
  for (let k = 1; k < path.length; k++) {
    if (v === null || typeof v !== 'object' || !Object.hasOwn(v, path[k])) return undefined;
    v = v[path[k]];
  }
  return v;
}

function textOf(v) {
  if (typeof v === 'string') return v;
  if (typeof v === 'number') return String(v);
  if (typeof v === 'boolean') return v ? 'true' : 'false';
  if (Array.isArray(v)) {
    let out = '';
    for (let i = 0; i < v.length; i++) { if (i > 0) out += ', '; out += textOf(v[i]); }
    return out;
  }
  return '';
}

function truthy(v) {
  if (Array.isArray(v)) return v.length > 0;
  return v !== undefined && v !== null && v !== false && v !== '' && v !== 0;
}

function renderNodes(nodes, scope, ctx, depth, out) {
  for (let ni = 0; ni < nodes.length; ni++) {
    const n = nodes[ni];
    if (n.kind === 'text') out.push(n.text);
    else if (n.kind === 'var') out.push(esc(textOf(lookup(scope, n.path))));
    else if (n.kind === 'raw') out.push(textOf(lookup(scope, n.path)));
    else if (n.kind === 'if') {
      const v = truthy(lookup(scope, n.path));
      const branch = v !== n.not ? n.then : n.else;
      if (branch !== null) renderNodes(branch, scope, ctx, depth, out);
    } else if (n.kind === 'for') {
      const xs = lookup(scope, n.path);
      if (Array.isArray(xs)) {
        // One scope object and one loop object per execution of the for,
        // mutated per element: rendering is synchronous and no template
        // ever keeps a scope, so reusing them is unobservable.
        const vars = {};
        const loop = { index: 0, first: false, last: false, length: xs.length };
        vars[n.name] = undefined;
        vars.loop = loop;
        const child = { vars, parent: scope };
        for (let k = 0; k < xs.length; k++) {
          vars[n.name] = xs[k];
          loop.index = k + 1;
          loop.first = k === 0;
          loop.last = k === xs.length - 1;
          renderNodes(n.body, child, ctx, depth, out);
        }
      }
    } else if (n.kind === 'include') {
      const t = ctx.templates.get(n.name);
      if (t !== undefined && depth < 8) renderNodes(t, scope, ctx, depth + 1, out);
    }
  }
}

// ---------------------------------------------------------------------- build

// Resolve a relative link target against a source directory, without
// splitting either side into arrays: '..' pops the last segment of the
// directory string, '.' and empty segments are skipped. Returns null
// when the target climbs above the root.
function resolvePathStr(dir, rel) {
  let out = dir;
  let i = 0;
  const n = rel.length;
  for (;;) {
    const j = rel.indexOf('/', i);
    const end = j === -1 ? n : j;
    const seg = rel.slice(i, end);
    if (seg === '..') {
      if (out === '') return null;
      const k = out.lastIndexOf('/');
      out = k === -1 ? '' : out.slice(0, k);
    } else if (seg !== '' && seg !== '.') {
      out = out === '' ? seg : out + '/' + seg;
    }
    if (j === -1) break;
    i = j + 1;
  }
  return out;
}

export function run(input) {
  slugCache = new Map();
  const templates = new Map();
  const report = [];
  for (const name of Object.keys(input.templates).sort(byCodeUnits)) {
    try {
      templates.set(name, parseTemplate(name, input.templates[name]));
    } catch (err) {
      if (!(err instanceof TemplateError)) throw err;
      report.push(err.message);
    }
  }
  const base = input.site.base_url.replace(/\/+$/, '');
  const files = [...input.files].sort((x, y) => byCodeUnits(x.path, y.path));
  const sources = [];
  const statics = [];
  for (const f of files) {
    if (f.path.endsWith('.md')) {
      sources.push({ path: f.path, text: f.content.indexOf('\r') === -1 ? f.content : f.content.replace(/\r\n?/g, '\n') });
    } else statics.push({ path: f.path, content: f.content });
  }
  const kept = [];
  for (const s of sources) {
    const fm = parseFrontMatter(s.text);
    if ('error' in fm) { report.push('refused ' + s.path + ': ' + fm.error); continue; }
    s.data = fm.data;
    s.body = fm.body;
    s.post = s.path.startsWith('posts/');
    let own = null;
    if (s.path.startsWith('tags/')) own = 'tags';
    else if (s.path.startsWith('page/')) own = 'page';
    if (own !== null) { report.push('refused ' + s.path + ': ' + own + '/ is the generator\'s own'); continue; }
    if (s.post && !Object.hasOwn(s.data, 'date')) { report.push('refused ' + s.path + ': a post needs a date'); continue; }
    const layout = s.data.layout !== undefined ? s.data.layout : (s.post ? 'post' : 'page');
    if (!templates.has(layout)) { report.push('refused ' + s.path + ': layout "' + layout + '" is no template that parses'); continue; }
    s.layout = layout;
    if (s.data.draft === true) { report.push('draft ' + s.path); continue; }
    kept.push(s);
  }
  const taken = new Map();
  const bySource = new Map();
  const output = {};
  for (const s of kept) {
    const dir = s.post ? 'posts' : dirOf(s.path);
    let set = taken.get(dir);
    if (set === undefined) { set = new Set(dir === '' ? RESERVED : []); taken.set(dir, set); }
    const slug = uniqueSlug(s.data.slug !== undefined ? s.data.slug : slugify(s.data.title), set);
    s.slug = slug;
    s.outDir = dir === '' ? slug : dir + '/' + slug;
    s.url = base + '/' + s.outDir + '/';
    bySource.set(s.path, s);
  }
  const staticPaths = new Set();
  for (const f of statics) staticPaths.add(f.path);
  const broken = new Set();
  for (const s of kept) {
    const dir = dirOf(s.path);
    const env = {
      link: (target) => {
        const c0 = target.charCodeAt(0);
        if (c0 === 47 || c0 === 35) return target; // '/' or '#'
        // A scheme is a letter, then [A-Za-z0-9+.-]*, then ':'.
        if ((c0 >= 65 && c0 <= 90) || (c0 >= 97 && c0 <= 122)) {
          let j = 1;
          while (j < target.length) {
            const c = target.charCodeAt(j);
            if ((c >= 65 && c <= 90) || (c >= 97 && c <= 122) || (c >= 48 && c <= 57) || c === 43 || c === 45 || c === 46) j++;
            else break;
          }
          if (target.charCodeAt(j) === 58) return target;
        }
        const hash = target.indexOf('#');
        const rel = hash === -1 ? target : target.slice(0, hash);
        const frag = hash === -1 ? '' : target.slice(hash);
        const path = rel === '' ? null : resolvePathStr(dir, rel);
        if (path !== null && bySource.has(path)) return bySource.get(path).url + frag;
        if (path !== null && staticPaths.has(path)) return base + '/' + path + frag;
        broken.add('broken-link ' + s.path + ' -> ' + target);
        return target;
      },
    };
    const md = renderMarkdown(s.body, env);
    s.html = md.html;
    s.toc = md.toc;
    s.excerpt = md.excerpt;
    s.words = md.words;
  }
  const posts = [];
  for (const s of kept) if (s.post) posts.push(s);
  posts.sort((x, y) => byCodeUnits(y.data.date, x.data.date) || byCodeUnits(x.slug, y.slug));
  for (let k = 0; k < posts.length; k++) {
    posts[k].newer = k === 0 ? null : posts[k - 1];
    posts[k].older = k === posts.length - 1 ? null : posts[k + 1];
  }
  const bySlug = new Map();
  const ownTags = (s) => {
    const seen = new Set();
    const out = [];
    const tags = s.data.tags !== undefined ? s.data.tags : [];
    for (const name of tags) {
      const slug = slugify(name);
      if (!seen.has(slug)) { seen.add(slug); out.push(name); }
    }
    return out;
  };
  for (const p of posts) {
    p.tagRefs = [];
    for (const name of ownTags(p)) {
      const slug = slugify(name);
      let tag = bySlug.get(slug);
      if (tag === undefined) {
        tag = { name, slug, url: base + '/tags/' + slug + '/', posts: [] };
        bySlug.set(slug, tag);
      }
      tag.posts.push(p);
      p.tagRefs.push(tag);
    }
  }
  for (const s of kept) {
    if (s.post) continue;
    s.tagRefs = [];
    for (const name of ownTags(s)) {
      const slug = slugify(name);
      const t = bySlug.get(slug);
      s.tagRefs.push(t !== undefined ? t : { name, slug, url: '', posts: [] });
    }
  }
  const tags = [...bySlug.values()].sort((x, y) => y.posts.length - x.posts.length || byCodeUnits(x.slug, y.slug));
  const cardOf = (s) => ({
    title: s.data.title,
    url: s.url,
    date: s.data.date !== undefined ? s.data.date : '',
    date_long: s.data.date === undefined ? '' : longDate(s.data.date),
    summary: s.data.summary !== undefined ? s.data.summary : '',
    excerpt: s.excerpt,
    reading_minutes: Math.max(1, Math.ceil(s.words / 200)),
    tags: s.tagRefs.map((t) => {
      if (t.link === undefined) t.link = { name: t.name, slug: t.slug, url: t.url };
      return t.link;
    }),
  });
  const cards = new Map();
  for (const p of posts) cards.set(p, cardOf(p));
  const linkOf = (s) => s === null ? null : {
    title: s.data.title, url: s.url,
    date: s.data.date !== undefined ? s.data.date : '',
    date_long: s.data.date === undefined ? '' : longDate(s.data.date),
  };
  const pageOf = (s) => {
    const card = s.post ? cards.get(s) : cardOf(s);
    return {
      ...card,
      slug: s.slug,
      content: s.html,
      // The toc entries already have exactly the output shape
      // {level, id, html} and nothing mutates them, so no copy is needed.
      toc: s.toc,
      newer: linkOf(s.newer !== undefined && s.newer !== null ? s.newer : null),
      older: linkOf(s.older !== undefined && s.older !== null ? s.older : null),
      is_post: s.post,
    };
  };
  const site = { title: input.site.title, base_url: base };
  const allTags = tags.map((t) => ({ name: t.name, slug: t.slug, url: t.url, count: t.posts.length }));
  const recent = posts.slice(0, input.site.recent).map((p) => cards.get(p));
  const ctx = { templates };
  // One scope for the case-wide names (site/tags/recent); each render
  // hangs its own vars off it instead of copying the case-wide names
  // into a fresh object per page. The render vars (page/posts/tag/pager)
  // never collide with the case-wide names, so lookups resolve the same.
  const baseScope = { vars: { site, tags: allTags, recent }, parent: null };
  const render = (name, vars) => {
    const nodes = templates.get(name);
    if (nodes === undefined) return null;
    const out = [];
    renderNodes(nodes, { vars, parent: baseScope }, ctx, 0, out);
    return out.join('');
  };
  for (const s of kept) output[s.outDir + '/index.html'] = render(s.layout, { page: pageOf(s) });
  const per = input.site.per_page;
  const pages = Math.max(1, Math.ceil(posts.length / per));
  const indexUrl = (k) => (k === 1 ? base + '/' : base + '/page/' + k + '/');
  for (let k = 1; k <= pages; k++) {
    const html = render('index', {
      posts: posts.slice((k - 1) * per, k * per).map((p) => cards.get(p)),
      pager: { number: k, total: pages, url: indexUrl(k), newer_url: k === 1 ? '' : indexUrl(k - 1), older_url: k === pages ? '' : indexUrl(k + 1) },
    });
    if (html !== null) output[k === 1 ? 'index.html' : 'page/' + k + '/index.html'] = html;
  }
  for (const t of tags) {
    const html = render('tag', { tag: { name: t.name, slug: t.slug, url: t.url, count: t.posts.length, posts: t.posts.map((p) => cards.get(p)) } });
    if (html !== null) output['tags/' + t.slug + '/index.html'] = html;
  }
  const tagsHtml = render('tags', {});
  if (tagsHtml !== null) output['tags/index.html'] = tagsHtml;
  for (const f of statics) {
    if (Object.hasOwn(output, f.path)) report.push('shadowed ' + f.path + ': a built page has its path');
    else output[f.path] = f.content;
  }
  const lines = [...report, ...broken].sort(byCodeUnits);
  let pageCount = 0;
  for (const s of kept) if (!s.post) pageCount++;
  lines.push('built ' + pageCount + ' pages, ' + posts.length + ' posts, ' + tags.length + ' tags and ' + statics.length + ' static files');
  output['build-report.txt'] = lines.join('\n') + '\n';
  return output;
}
