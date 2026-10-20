#!/usr/bin/env python3
"""
DevToolkit - 10 developer utilities in one desktop app.

  1  JSON to Java           5  SQL to Java Models      9  Regex Tester
  2  JSON to TypeScript     6  CSV to JSON            10  Cron Expression Generator
  3  XML to JSON            7  Base64 Encoder/Decoder
  4  YAML to JSON           8  URL Encoder/Decoder

Run:  python dev_toolkit.py
Needs Python 3.8+ only (Tkinter ships with the Windows/macOS installers).
Optional: "pip install pyyaml" gives full YAML support; without it a built-in
parser handles everyday YAML (maps, lists, nested blocks, quoted strings).
Everything runs locally - nothing is uploaded anywhere.
"""
import base64
import csv
import io
import json
import os
import re
import subprocess
import sys
import time
import urllib.parse
import xml.etree.ElementTree as ET
from datetime import date, datetime, timedelta

import tkinter as tk
from tkinter import filedialog, ttk


# ======================================================================
#  PART 1 - CONVERSION LOGIC (no GUI code in this part)
# ======================================================================

# ---------------------------------------------------------------- names
JAVA_KEYWORDS = set("""abstract assert boolean break byte case catch char class const continue
default do double else enum extends final finally float for goto if implements import instanceof
int interface long native new package private protected public return short static strictfp super
switch synchronized this throw throws transient try void volatile while true false null var
record""".split())


def _words(name):
    return re.findall(r"[A-Za-z0-9]+", str(name))


def pascal(name):
    out = "".join(p[:1].upper() + p[1:] for p in _words(name)) or "Field"
    return "_" + out if out[0].isdigit() else out


def camel(name):
    parts = _words(name)
    if not parts:
        return "field"
    first = parts[0].lower() if parts[0].isupper() else parts[0][:1].lower() + parts[0][1:]
    out = first + "".join(p[:1].upper() + p[1:] for p in parts[1:])
    if out[0].isdigit():
        out = "_" + out
    return out + "_" if out in JAVA_KEYWORDS else out


def singular(name):
    low = name.lower()
    if low.endswith("ies") and len(name) > 4:
        return name[:-3] + "y"
    if low.endswith(("ses", "xes", "ches", "shes")) and len(name) > 4:
        return name[:-2]
    if low.endswith("s") and not low.endswith(("ss", "us", "is")) and len(name) > 3:
        return name[:-1]
    return name


def _cap(s):
    return s[:1].upper() + s[1:]


# ------------------------------------------------------- type inference
# A "descriptor" is a tuple: ("str",) ("int",) ("long",) ("double",) ("bool",) ("null",)
# ("empty",) ("any",) ("nullable", d) ("list", d) ("obj", {key: (d, optional)})
_NUM = {"int": 0, "long": 1, "double": 2}


def infer(v):
    if v is None:
        return ("null",)
    if isinstance(v, bool):
        return ("bool",)
    if isinstance(v, int):
        return ("int",) if -2 ** 31 <= v < 2 ** 31 else ("long",)
    if isinstance(v, float):
        return ("double",)
    if isinstance(v, str):
        return ("str",)
    if isinstance(v, list):
        el = ("empty",)
        for x in v:
            el = merge(el, infer(x))
        return ("list", el)
    if isinstance(v, dict):
        return ("obj", {k: (infer(x), False) for k, x in v.items()})
    return ("any",)


def merge(a, b):
    if a == b:
        return a
    ka, kb = a[0], b[0]
    if ka == "empty":
        return b
    if kb == "empty":
        return a
    if ka == "null":
        return b if kb == "nullable" else ("nullable", b)
    if kb == "null":
        return merge(b, a)
    if ka == "nullable":
        return ("nullable", merge(a[1], b[1] if kb == "nullable" else b))
    if kb == "nullable":
        return merge(b, a)
    if ka in _NUM and kb in _NUM:
        return a if _NUM[ka] >= _NUM[kb] else b
    if ka == kb == "list":
        return ("list", merge(a[1], b[1]))
    if ka == kb == "obj":
        keys = {}
        for k in list(a[1]) + [k for k in b[1] if k not in a[1]]:
            if k in a[1] and k in b[1]:
                keys[k] = (merge(a[1][k][0], b[1][k][0]), a[1][k][1] or b[1][k][1])
            else:
                keys[k] = ((a[1].get(k) or b[1].get(k))[0], True)  # missing somewhere -> optional
        return ("obj", keys)
    return ("any",)


def _root_object(data):
    desc = infer(data)
    while desc[0] in ("list", "nullable"):
        desc = desc[1]
    if desc[0] != "obj":
        raise ValueError("The JSON must be an object, or an array of objects.")
    return desc


# ------------------------------------------------------------ JSON -> Java
class _Model:
    """Collects the classes found in a JSON structure (shared by Java and TypeScript output)."""

    def __init__(self):
        self.classes = {}  # name -> list of field tuples
        self._by_sig = {}

    def _unique(self, base):
        name, i = base, 2
        while name in self.classes:
            name, i = f"{base}{i}", i + 1
        return name

    def add_object(self, desc, hint):
        base = pascal(hint)
        sig = (base, repr(desc))
        if sig in self._by_sig:
            return self._by_sig[sig]
        name = self._unique(base)
        self._by_sig[sig] = name
        fields = []
        self.classes[name] = fields
        used = set()
        for key, (fd, optional) in desc[1].items():
            fields.append(self.make_field(key, fd, optional, used))
        return name

    def make_field(self, key, fd, optional, used):
        raise NotImplementedError


class _JavaModel(_Model):
    SIMPLE = {"str": "String", "bool": "Boolean", "int": "Integer", "long": "Long",
              "double": "Double", "null": "Object", "any": "Object", "empty": "Object"}

    def make_field(self, key, fd, optional, used):
        jt = self.java_type(fd, key)
        base = fname = camel(key)
        n = 2
        while fname in used:
            fname, n = f"{base}{n}", n + 1
        used.add(fname)
        return (key, jt, fname)

    def java_type(self, d, hint):
        k = d[0]
        if k in self.SIMPLE:
            return self.SIMPLE[k]
        if k == "nullable":
            return self.java_type(d[1], hint)
        if k == "list":
            return f"List<{self.java_type(d[1], singular(hint))}>"
        return self.add_object(d, hint)


def render_class(name, fields, package, style, imports=(), class_ann=()):
    """fields: list of (java_type, field_name, [annotation lines]).
    style: 0 = getters/setters, 1 = Lombok @Data, 2 = Java record."""
    imports = set(imports)
    if any("List<" in t for t, _, _ in fields):
        imports.add("java.util.List")
    if style == 1:
        imports.add("lombok.Data")
    lines = []
    if package:
        lines += [f"package {package};", ""]
    imps = sorted(imports, key=lambda s: (not s.startswith("java."), s))
    if imps:
        lines += [f"import {i};" for i in imps] + [""]
    ann = list(class_ann)
    if style == 2:
        params = ["    " + " ".join(a + [f"{t} {f}"]) for t, f, a in ((t, f, [x for x in an if not x.startswith("//")])
                                                                      for t, f, an in fields)]
        lines += ann + [f"public record {name}("] + [",\n".join(params)] + [") {}"]
        return "\n".join(lines) + "\n"
    if style == 1:
        ann.append("@Data")
    lines += ann + [f"public class {name} {{", ""]
    for t, f, anns in fields:
        lines += [f"    {a}" for a in anns] + [f"    private {t} {f};", ""]
    if style == 0:
        for t, f, _ in fields:
            lines += [f"    public {t} get{_cap(f)}() {{", f"        return {f};", "    }", "",
                      f"    public void set{_cap(f)}({t} {f}) {{", f"        this.{f} = {f};", "    }", ""]
    while lines and lines[-1] == "":
        lines.pop()
    lines.append("}")
    return "\n".join(lines) + "\n"


def json_to_java(text, root="Root", package="", style=0, jackson=True):
    """Returns a list of (file_name, source_code)."""
    desc = _root_object(json.loads(text))
    model = _JavaModel()
    model.add_object(desc, (root or "Root").strip() or "Root")
    files = []
    for name, fields in model.classes.items():
        out_fields, imports = [], set()
        for key, jt, fname in fields:
            anns = []
            if jackson and key != fname:
                anns.append(f'@JsonProperty({json.dumps(key)})')
                imports.add("com.fasterxml.jackson.annotation.JsonProperty")
            out_fields.append((jt, fname, anns))
        files.append((f"{name}.java", render_class(name, out_fields, package.strip(), style, imports)))
    return files


# ------------------------------------------------------- JSON -> TypeScript
class _TsModel(_Model):
    SIMPLE = {"str": "string", "bool": "boolean", "int": "number", "long": "number",
              "double": "number", "null": "null", "any": "any", "empty": "any"}

    def make_field(self, key, fd, optional, used):
        t = self.ts_type(fd, key)
        prop = key if re.fullmatch(r"[A-Za-z_$][\w$]*", key) else json.dumps(key)
        return (prop, t, optional)

    def ts_type(self, d, hint):
        k = d[0]
        if k in self.SIMPLE:
            return self.SIMPLE[k]
        if k == "nullable":
            return f"{self.ts_type(d[1], hint)} | null"
        if k == "list":
            el = self.ts_type(d[1], singular(hint))
            return f"({el})[]" if "|" in el else f"{el}[]"
        return self.add_object(d, hint)


def json_to_typescript(text, root="Root", kind="interface", export=True):
    desc = _root_object(json.loads(text))
    model = _TsModel()
    model.add_object(desc, (root or "Root").strip() or "Root")
    kw = "export " if export else ""
    blocks = []
    for name, fields in model.classes.items():
        body = [f"  {p}{'?' if opt else ''}: {t};" for p, t, opt in fields]
        if kind == "interface":
            blocks.append(f"{kw}interface {name} {{\n" + "\n".join(body) + "\n}")
        else:
            blocks.append(f"{kw}type {name} = {{\n" + "\n".join(body) + "\n};")
    return "\n\n".join(blocks) + "\n"


# ----------------------------------------------------------- shared helpers
_INT_RE = re.compile(r"[-+]?(0|[1-9]\d*)")
_FLOAT_RE = re.compile(r"[-+]?(\d+\.\d*|\.\d+|\d+)([eE][-+]?\d+)?")


def detect_value(s):
    """'12' -> 12, '3.5' -> 3.5, 'true' -> True, '' -> None; anything else stays a string."""
    t = s.strip()
    if t == "":
        return None
    if t.lower() in ("true", "false"):
        return t.lower() == "true"
    if _INT_RE.fullmatch(t):
        return int(t)
    if _FLOAT_RE.fullmatch(t) and ("." in t or "e" in t.lower()):
        return float(t)
    return s


def dump_json(obj, indent):
    return json.dumps(obj, indent=indent, ensure_ascii=False)


def read_text_file(path):
    with open(path, "rb") as fh:
        raw = fh.read()
    if raw[:2] in (b"\xff\xfe", b"\xfe\xff"):
        return raw.decode("utf-16")
    try:
        return raw.decode("utf-8-sig")
    except UnicodeDecodeError:
        return raw.decode("cp1252", errors="replace")


# ---------------------------------------------------------------- XML -> JSON
def _strip_ns(tag):
    return re.sub(r"^\{[^}]*\}", "", tag)


def _xml_node(el, attrs, detect):
    conv = detect_value if detect else (lambda s: s)
    node = {}
    if attrs:
        for k, v in el.attrib.items():
            node["@" + _strip_ns(k)] = conv(v)
    for child in el:
        if not isinstance(child.tag, str):
            continue  # comments / processing instructions
        tag = _strip_ns(child.tag)
        val = _xml_node(child, attrs, detect)
        if tag in node:
            if isinstance(node[tag], list):
                node[tag].append(val)
            else:
                node[tag] = [node[tag], val]
        else:
            node[tag] = val
    text = (el.text or "").strip()
    if not node:
        return conv(text) if text else None
    if text:
        node["#text"] = conv(text)
    return node


def xml_to_json(text, indent=2, attrs=True, detect=False):
    try:
        root = ET.fromstring(text.strip())
    except ET.ParseError as e:
        raise ValueError(f"Invalid XML: {e}")
    return dump_json({_strip_ns(root.tag): _xml_node(root, attrs, detect)}, indent)


# --------------------------------------------------------------- YAML -> JSON
def _yaml_strip_comment(line):
    out, quote = [], None
    for i, ch in enumerate(line):
        if quote:
            out.append(ch)
            if ch == quote:
                quote = None
        elif ch in "\"'" and (i == 0 or line[i - 1] in " \t[{,:-"):
            out.append(ch)
            quote = ch
        elif ch == "#" and (i == 0 or line[i - 1] in " \t"):
            break
        else:
            out.append(ch)
    return "".join(out).rstrip()


def _yaml_scalar(s):
    s = s.strip()
    if s == "" or s == "~" or s.lower() == "null":
        return None
    if len(s) >= 2 and s[0] == '"' and s[-1] == '"':
        try:
            return json.loads(s)
        except ValueError:
            return s[1:-1]
    if len(s) >= 2 and s[0] == "'" and s[-1] == "'":
        return s[1:-1].replace("''", "'")
    if s.lower() in ("true", "false"):
        return s.lower() == "true"
    if _INT_RE.fullmatch(s):
        return int(s)
    if _FLOAT_RE.fullmatch(s) and ("." in s or "e" in s.lower()):
        return float(s)
    return s


def _split_key(s):
    """Return (key, rest) when s looks like 'key: value' / 'key:', else None."""
    if not s or s[0] in "[{":
        return None
    if s[0] in "\"'":
        q = s[0]
        end = s.find(q, 1)
        if end == -1:
            return None
        after = s[end + 1:]
        if after.startswith(":") and (len(after) == 1 or after[1] == " "):
            return s[1:end], after[1:].strip()
        return None
    m = re.match(r"^(.*?):(\s+(.*))?$", s)
    if not m:
        return None
    return m.group(1).strip(), (m.group(3) or "").strip()


def _parse_flow(s):
    pos = 0

    def ws():
        nonlocal pos
        while pos < len(s) and s[pos] in " \t":
            pos += 1

    def token(stop):
        nonlocal pos
        ws()
        if s[pos] in "\"'":
            q, start = s[pos], pos
            pos += 1
            while s[pos] != q:
                pos += 1
            pos += 1
            return _yaml_scalar(s[start:pos])
        start = pos
        while pos < len(s) and s[pos] not in stop:
            pos += 1
        return _yaml_scalar(s[start:pos])

    def value():
        nonlocal pos
        ws()
        if s[pos] == "[":
            pos += 1
            items = []
            while True:
                ws()
                if s[pos] == "]":
                    pos += 1
                    return items
                items.append(value())
                ws()
                if s[pos] == ",":
                    pos += 1
                elif s[pos] != "]":
                    raise ValueError("bad list")
        if s[pos] == "{":
            pos += 1
            result = {}
            while True:
                ws()
                if s[pos] == "}":
                    pos += 1
                    return result
                key = token(":,}")
                ws()
                if s[pos] != ":":
                    raise ValueError("bad map")
                pos += 1
                result[str(key)] = value()
                ws()
                if s[pos] == ",":
                    pos += 1
                elif s[pos] != "}":
                    raise ValueError("bad map")
        return token(",]}")

    try:
        return value()
    except (IndexError, ValueError):
        raise ValueError(f"Cannot read the inline value: {s}")


def _fold_lines(block):
    out = ""
    for ln in block:
        if ln == "":
            out += "\n"
        elif out and not out.endswith("\n"):
            out += " " + ln
        else:
            out += ln
    return out


def mini_yaml_load(text):
    """Small YAML reader: block maps/lists, nesting, quoted strings, [a, b] / {a: b}, | and > blocks."""
    if re.search(r"(^|[\s:\-])[&*][A-Za-z_]", text) or re.search(r"(^|\s)!!?\w", text):
        raise ValueError("Anchors, aliases and tags need the full parser - run: pip install pyyaml")
    raw_lines = text.expandtabs(2).splitlines()
    lines = []  # (indent, content, raw, raw_index)
    for idx, raw in enumerate(raw_lines):
        s = _yaml_strip_comment(raw)
        if not s.strip() or s.strip() in ("---", "..."):
            continue
        lines.append((len(s) - len(s.lstrip(" ")), s.strip(), raw, idx))
    if not lines:
        return None
    pos = 0
    BLOCK = ("|", ">", "|-", ">-", "|+", ">+")

    def is_dash(c):
        return c == "-" or c.startswith("- ")

    def read_block(style, parent_indent, idx):
        nonlocal pos
        block, j, block_indent = [], idx + 1, None
        while j < len(raw_lines):
            raw = raw_lines[j]
            if raw.strip() == "":
                block.append("")
                j += 1
                continue
            ind = len(raw) - len(raw.lstrip(" "))
            if ind <= parent_indent:
                break
            if block_indent is None:
                block_indent = ind
            block.append(raw[block_indent:] if ind >= block_indent else raw.strip())
            j += 1
        while pos < len(lines) and lines[pos][3] < j:
            pos += 1
        while block and block[-1] == "":
            block.pop()
        body = "\n".join(block) if style.startswith("|") else _fold_lines(block)
        return body if style.endswith("-") else body + "\n"

    def inline(rest):
        return _parse_flow(rest) if rest[:1] in ("[", "{") else _yaml_scalar(rest)

    def parse_block():
        nonlocal pos
        indent, content = lines[pos][0], lines[pos][1]
        if is_dash(content):
            return parse_list(indent)
        if _split_key(content) is not None:
            return parse_map(indent)
        pos += 1
        return inline(content)

    def parse_map(indent):
        nonlocal pos
        result = {}
        while pos < len(lines) and lines[pos][0] == indent and not is_dash(lines[pos][1]):
            content, idx = lines[pos][1], lines[pos][3]
            kv = _split_key(content)
            if kv is None:
                raise ValueError(f"Cannot understand this line: {content}")
            key, rest = kv
            pos += 1
            if rest in BLOCK:
                result[key] = read_block(rest, indent, idx)
            elif rest == "":
                nxt = lines[pos] if pos < len(lines) else None
                if nxt and (nxt[0] > indent or (nxt[0] == indent and is_dash(nxt[1]))):
                    result[key] = parse_block()
                else:
                    result[key] = None
            else:
                result[key] = inline(rest)
        if pos < len(lines) and lines[pos][0] > indent:
            raise ValueError(f"Unexpected indentation near: {lines[pos][1]}")
        return result

    def parse_list(indent):
        nonlocal pos
        items = []
        while pos < len(lines) and lines[pos][0] == indent and is_dash(lines[pos][1]):
            _ind, content, raw, idx = lines[pos]
            rest = content[1:].strip()
            if rest == "":
                pos += 1
                items.append(parse_block() if pos < len(lines) and lines[pos][0] > indent else None)
            elif is_dash(rest) or (rest[0] not in "[{" and _split_key(rest) is not None):
                offset = content.index(rest)  # treat the text after "- " as a deeper-indented line
                lines[pos] = (indent + offset, rest, raw, idx)
                items.append(parse_block())
            else:
                pos += 1
                items.append(read_block(rest, indent, idx) if rest in BLOCK else inline(rest))
        return items

    result = parse_block()
    if pos < len(lines):
        raise ValueError(f"Unexpected content near: {lines[pos][1]} (check the indentation)")
    return result


def _jsonable(o):
    if isinstance(o, dict):
        return {(k if isinstance(k, (str, int, float, bool)) or k is None else str(k)): _jsonable(v)
                for k, v in o.items()}
    if isinstance(o, (list, tuple, set)):
        return [_jsonable(v) for v in o]
    if isinstance(o, (datetime, date)):
        return o.isoformat()
    if isinstance(o, (str, int, float, bool)) or o is None:
        return o
    return str(o)


def yaml_to_json(text, indent=2):
    """Returns (json_text, used_builtin_parser)."""
    try:
        import yaml  # optional
    except ImportError:
        yaml = None
    if yaml is not None:
        try:
            docs = list(yaml.safe_load_all(text))
        except yaml.YAMLError as e:
            raise ValueError(f"Invalid YAML: {e}")
        data = docs[0] if len(docs) == 1 else docs
        return dump_json(_jsonable(data), indent), False
    return dump_json(_jsonable(mini_yaml_load(text)), indent), True


# ------------------------------------------------------------- SQL -> Java
_CONSTRAINT = re.compile(
    r"^(PRIMARY\s+KEY|FOREIGN\s+KEY|CONSTRAINT\b|CHECK\s*\(|UNIQUE\s*\(|UNIQUE\s+(KEY|INDEX)\b|"
    r"(KEY|INDEX)\s+[`\"\[]?\w+[`\"\]]?\s*\(|FULLTEXT\b|SPATIAL\b)", re.I)


def _split_top_level(body):
    parts, depth, cur, quote = [], 0, [], None
    for ch in body:
        if quote:
            cur.append(ch)
            if ch == quote:
                quote = None
            continue
        if ch in "'\"`":
            quote = ch
            cur.append(ch)
            continue
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        if ch == "," and depth == 0:
            parts.append("".join(cur).strip())
            cur = []
        else:
            cur.append(ch)
    if "".join(cur).strip():
        parts.append("".join(cur).strip())
    return parts


def _ident(tok):
    pieces = [p.strip().strip('`"[]') for p in tok.strip().split(".")]
    return pieces[-1]


def _sql_java_type(base, args, tz):
    b = base.upper()
    if b == "TINYINT" and args.strip() == "1" or b in ("BOOLEAN", "BOOL", "BIT"):
        return "Boolean", None
    if b in ("BIGINT", "BIGSERIAL", "INT8", "SERIAL8"):
        return "Long", None
    if b in ("INT", "INTEGER", "SMALLINT", "TINYINT", "MEDIUMINT", "SERIAL", "SMALLSERIAL", "INT2", "INT4"):
        return "Integer", None
    if b in ("DECIMAL", "NUMERIC", "NUMBER", "MONEY", "SMALLMONEY", "DEC"):
        return "BigDecimal", "java.math.BigDecimal"
    if b in ("FLOAT", "REAL", "FLOAT4"):
        return "Float", None
    if b in ("DOUBLE", "DOUBLE PRECISION", "FLOAT8"):
        return "Double", None
    if b == "DATE":
        return "LocalDate", "java.time.LocalDate"
    if b in ("TIME", "TIMETZ"):
        return "LocalTime", "java.time.LocalTime"
    if b in ("TIMESTAMPTZ", "DATETIMEOFFSET") or (b in ("TIMESTAMP", "DATETIME") and tz):
        return "OffsetDateTime", "java.time.OffsetDateTime"
    if b in ("TIMESTAMP", "DATETIME", "DATETIME2", "SMALLDATETIME"):
        return "LocalDateTime", "java.time.LocalDateTime"
    if b == "UUID":
        return "UUID", "java.util.UUID"
    if "BLOB" in b or b in ("BYTEA", "BINARY", "VARBINARY", "IMAGE", "RAW"):
        return "byte[]", None
    return "String", None


def parse_sql_tables(sql):
    sql = re.sub(r"--[^\n]*", "", sql)
    sql = re.sub(r"/\*.*?\*/", "", sql, flags=re.S)
    tables = []
    pattern = r"CREATE\s+(?:OR\s+REPLACE\s+)?(?:TEMP(?:ORARY)?\s+)?TABLE\s+(?:IF\s+NOT\s+EXISTS\s+)?([^\s(]+)\s*\("
    for m in re.finditer(pattern, sql, re.I):
        start, depth, i, quote = m.end(), 1, m.end(), None
        while i < len(sql) and depth:
            ch = sql[i]
            if quote:
                if ch == quote:
                    quote = None
            elif ch in "'\"`":
                quote = ch
            elif ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
            i += 1
        body = sql[start:i - 1]
        cols, pk_cols = [], []
        for part in _split_top_level(body):
            if _CONSTRAINT.match(part):
                pm = re.search(r"PRIMARY\s+KEY\s*\(([^)]*)\)", part, re.I)
                if pm:
                    pk_cols += [_ident(c) for c in pm.group(1).split(",") if c.strip()]
                continue
            cm = re.match(r"^\s*(\"[^\"]+\"|`[^`]+`|\[[^\]]+\]|[\w$]+)\s*(.*)$", part, re.S)
            if not cm:
                continue
            name, rest = _ident(cm.group(1)), cm.group(2).strip()
            tm = re.match(r"([A-Za-z_]\w*)", rest)
            if not tm:
                continue
            base, pos = tm.group(1).upper(), tm.end()
            for extra in ("VARYING", "PRECISION"):
                em = re.match(r"\s+" + extra + r"\b", rest[pos:], re.I)
                if em:
                    base += " " + extra
                    pos += em.end()
            am = re.match(r"\s*\(([^)]*)\)", rest[pos:])
            args = am.group(1) if am else ""
            if am:
                pos += am.end()
            zm = re.match(r"\s+WITH(OUT)?\s+TIME\s+ZONE", rest[pos:], re.I)
            tz = bool(zm) and not zm.group(1)
            if zm:
                pos += zm.end()
            flags = rest[pos:].upper()
            jtype, imp = _sql_java_type(base, args, tz)
            auto = bool(re.search(r"AUTO_?INCREMENT|IDENTITY|GENERATED", flags)) or base.endswith("SERIAL") \
                or base == "SERIAL"
            length = None
            if jtype == "String" and re.fullmatch(r"\s*\d+\s*", args):
                length = int(args)
            cols.append({"name": name, "jtype": jtype, "import": imp, "auto": auto, "length": length,
                         "pk": "PRIMARY KEY" in flags, "notnull": "NOT NULL" in flags})
        for c in cols:
            if c["name"] in pk_cols:
                c["pk"] = True
        tables.append({"name": _ident(m.group(1)), "columns": cols})
    return tables


def sql_to_java(sql, package="", jpa=True, jpa_ns="jakarta.persistence", lombok=False):
    tables = parse_sql_tables(sql)
    if not tables:
        raise ValueError("No CREATE TABLE statement found. Paste one or more CREATE TABLE ... ( ... ); statements.")
    files = []
    for t in tables:
        cname = singular(pascal(t["name"]))
        cols = t["columns"]
        pks = [c for c in cols if c["pk"]]
        imports, fields, used = set(), [], set()
        class_ann = []
        if jpa:
            imports |= {f"{jpa_ns}.Entity", f"{jpa_ns}.Table", f"{jpa_ns}.Column"}
            class_ann = ["@Entity", f'@Table(name = "{t["name"]}")']
            if len(pks) > 1:
                class_ann.insert(0, "// NOTE: composite primary key - add @IdClass or @EmbeddedId")
        for idx, c in enumerate(cols):
            base = fname = camel(c["name"])
            n = 2
            while fname in used:
                fname, n = f"{base}{n}", n + 1
            used.add(fname)
            anns = []
            if jpa:
                is_id = c["pk"] or (not pks and idx == 0)
                if not pks and idx == 0:
                    anns.append("// TODO: no primary key found in the table - JPA needs an @Id")
                if is_id:
                    anns.append("@Id")
                    imports.add(f"{jpa_ns}.Id")
                if c["auto"] and is_id:
                    anns.append("@GeneratedValue(strategy = GenerationType.IDENTITY)")
                    imports |= {f"{jpa_ns}.GeneratedValue", f"{jpa_ns}.GenerationType"}
                attrs = [f'name = "{c["name"]}"']
                if c["notnull"] and not c["pk"]:
                    attrs.append("nullable = false")
                if c["length"]:
                    attrs.append(f"length = {c['length']}")
                anns.append(f"@Column({', '.join(attrs)})")
            if c["import"]:
                imports.add(c["import"])
            fields.append((c["jtype"], fname, anns))
        files.append((f"{cname}.java", render_class(cname, fields, package.strip(), 1 if lombok else 0,
                                                    imports, class_ann)))
    return files


# ------------------------------------------------------------- CSV -> JSON
def csv_to_json(text, delimiter="auto", header=True, detect=True, indent=2):
    if delimiter == "auto":
        try:
            delimiter = csv.Sniffer().sniff(text[:4096], delimiters=",;\t|").delimiter
        except csv.Error:
            delimiter = ","
    rows = [r for r in csv.reader(io.StringIO(text), delimiter=delimiter) if any(c.strip() for c in r)]
    if not rows:
        raise ValueError("No rows found.")
    width = max(len(r) for r in rows)
    if header:
        names, seen = [], {}
        for i in range(width):
            raw = rows[0][i].strip() if i < len(rows[0]) else ""
            name = raw or f"column{i + 1}"
            seen[name] = seen.get(name, 0) + 1
            names.append(name if seen[name] == 1 else f"{name}_{seen[name]}")
        data = rows[1:]
    else:
        names = [f"column{i + 1}" for i in range(width)]
        data = rows
    conv = detect_value if detect else (lambda s: s)
    records = [{names[i]: conv(r[i]) if i < len(r) else None for i in range(width)} for r in data]
    return dump_json(records, indent), delimiter, len(records)


# ------------------------------------------------------------------ Base64
def b64_encode(data, urlsafe=False):
    return (base64.urlsafe_b64encode if urlsafe else base64.b64encode)(data).decode("ascii")


def b64_decode_bytes(text, urlsafe=False):
    s = re.sub(r"\s+", "", text)
    if s.lower().startswith("data:") and "base64," in s:
        s = s.split("base64,", 1)[1]
    if urlsafe or "-" in s or "_" in s:
        s = s.replace("-", "+").replace("_", "/")
    s += "=" * (-len(s) % 4)
    try:
        return base64.b64decode(s, validate=True)
    except Exception:
        raise ValueError("This is not valid Base64 text.")


def b64_decode_text(text, urlsafe=False):
    raw = b64_decode_bytes(text, urlsafe)
    try:
        return raw.decode("utf-8")
    except UnicodeDecodeError:
        raise ValueError("The decoded data is binary, not text. Use 'Decode to file...' to save it.")


# --------------------------------------------------------------------- URL
URL_MODES = ["Component (encodeURIComponent)", "Full URL (encodeURI)", "Form (+ for spaces)"]


def url_encode(text, mode=0):
    if mode == 0:
        return urllib.parse.quote(text, safe="-_.!~*'()")
    if mode == 1:
        return urllib.parse.quote(text, safe=";/?:@&=+$,#-_.!~*'()")
    return urllib.parse.quote_plus(text, safe="")


def url_decode(text, mode=0):
    if mode == 2:
        return urllib.parse.unquote_plus(text, errors="replace")
    return urllib.parse.unquote(text, errors="replace")


def url_parse(text):
    u = urllib.parse.urlsplit(text.strip())
    lines = []
    for label, value in (("Scheme", u.scheme), ("Host", u.hostname), ("Port", u.port),
                         ("User", u.username), ("Path", u.path), ("Fragment", u.fragment)):
        if value not in (None, ""):
            lines.append(f"{label:<9}: {value}")
    params = urllib.parse.parse_qsl(u.query, keep_blank_values=True)
    if params:
        lines += ["", f"Query parameters ({len(params)}):"]
        width = max(len(k) for k, _ in params)
        lines += [f"  {k:<{width}} = {v}" for k, v in params]
    if not lines:
        raise ValueError("Nothing to parse - paste a URL or a query string.")
    return "\n".join(lines)


# -------------------------------------------------------------------- Regex
def regex_flags(i=False, m=False, s=False, x=False):
    return (re.I if i else 0) | (re.M if m else 0) | (re.S if s else 0) | (re.X if x else 0)


# --------------------------------------------------------------------- Cron
MONTH_SHORT = ["JAN", "FEB", "MAR", "APR", "MAY", "JUN", "JUL", "AUG", "SEP", "OCT", "NOV", "DEC"]
DOW_SHORT = ["SUN", "MON", "TUE", "WED", "THU", "FRI", "SAT"]
MONTH_NAMES = ["January", "February", "March", "April", "May", "June", "July", "August",
               "September", "October", "November", "December"]
DOW_NAMES = ["Sunday", "Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday"]
CRON_SPECIAL = {"@yearly": "0 0 1 1 *", "@annually": "0 0 1 1 *", "@monthly": "0 0 1 * *",
                "@weekly": "0 0 * * 0", "@daily": "0 0 * * *", "@midnight": "0 0 * * *", "@hourly": "0 * * * *"}
CRON_FIELDS = [("Minute", 0, 59, None, "0-59"), ("Hour", 0, 23, None, "0-23"),
               ("Day of month", 1, 31, None, "1-31"), ("Month", 1, 12, MONTH_SHORT, "1-12 / JAN-DEC"),
               ("Day of week", 0, 7, DOW_SHORT, "0-6 / SUN-SAT")]
CRON_PRESETS = [("Every minute", "* * * * *"), ("Every 5 minutes", "*/5 * * * *"),
                ("Every 15 minutes", "*/15 * * * *"), ("Hourly", "0 * * * *"),
                ("Daily at midnight", "0 0 * * *"), ("Daily at 09:00", "0 9 * * *"),
                ("Weekdays at 09:00", "0 9 * * 1-5"), ("Mondays at 08:00", "0 8 * * 1"),
                ("Monthly (1st)", "0 0 1 * *"), ("Yearly (Jan 1st)", "0 0 1 1 *")]


def parse_cron_field(text, lo, hi, names=None):
    values = set()
    for part in text.split(","):
        part = part.strip()
        if not part:
            raise ValueError("empty item in a list")
        step = 1
        if "/" in part:
            part, s = part.split("/", 1)
            if not s.isdigit() or int(s) == 0:
                raise ValueError(f"bad step '/{s}'")
            step = int(s)

        def num(t):
            t = t.strip()
            if names and t.upper() in names:
                return names.index(t.upper()) + (1 if lo == 1 else 0)
            if not t.isdigit():
                raise ValueError(f"'{t}' is not a number")
            n = int(t)
            if not lo <= n <= hi:
                raise ValueError(f"{n} is outside {lo}-{hi}")
            return n

        if part in ("*", "?"):
            a, b = lo, (6 if hi == 7 else hi)
        elif "-" in part:
            x, y = part.split("-", 1)
            a, b = num(x), num(y)
            if a > b:
                raise ValueError(f"range {part} is backwards")
        else:
            a = num(part)
            b = (6 if hi == 7 else hi) if step > 1 else a
        values.update(range(a, b + 1, step))
    if hi == 7:
        values = {0 if v == 7 else v for v in values}
    return values


def _cron_parts(expr):
    expr = CRON_SPECIAL.get(expr.strip().lower(), expr)
    f = expr.split()
    if len(f) != 5:
        raise ValueError("A cron expression needs 5 fields: minute hour day-of-month month day-of-week")
    sets = []
    for value, (name, lo, hi, names, _hint) in zip(f, CRON_FIELDS):
        try:
            sets.append(parse_cron_field(value, lo, hi, names))
        except ValueError as e:
            raise ValueError(f"{name}: {e}")
    return f, sets


def _join_and(items):
    return items[0] if len(items) == 1 else ", ".join(items[:-1]) + " and " + items[-1]


def _compress(values, label):
    vals, runs, i = sorted(values), [], 0
    while i < len(vals):
        j = i
        while j + 1 < len(vals) and vals[j + 1] == vals[j] + 1:
            j += 1
        if j - i >= 2:
            runs.append(f"{label(vals[i])} through {label(vals[j])}")
        else:
            runs += [label(v) for v in vals[i:j + 1]]
        i = j + 1
    return _join_and(runs)


def describe_cron(expr):
    f, (mins, hours, doms, mons, dows) = _cron_parts(expr)
    minute, hour, dom, mon, dow = f
    step = re.compile(r"\*/(\d+)$")

    def phrase(field, vals, unit, label=str):
        m = step.match(field)
        if field in ("*", "?"):
            return f"every {unit}"
        if m:
            return f"every {m.group(1)} {unit}s" if m.group(1) != "1" else f"every {unit}"
        return f"{unit}{'s' if len(vals) > 1 else ''} {_compress(vals, label)}"

    if len(mins) == 1 and len(hours) == 1:
        text = f"At {min(hours):02d}:{min(mins):02d}"
    elif minute in ("*", "?") or step.match(minute):
        text = phrase(minute, mins, "minute").capitalize()
        if hour not in ("*", "?"):
            text += ", during " + phrase(hour, hours, "hour", lambda v: f"{v:02d}:00") \
                .replace("every hour", "every hour")
    else:
        text = f"At {phrase(minute, mins, 'minute')} past {phrase(hour, hours, 'hour')}"
    day_bits = []
    dom_star, dow_star = dom in ("*", "?"), dow in ("*", "?")
    if not dom_star:
        m = step.match(dom)
        day_bits.append(f"on every {m.group(1)}th day of the month" if m
                        else f"on day {_compress(doms, str)} of the month")
    if not dow_star:
        day_bits.append("on " + _compress(dows, lambda v: DOW_NAMES[v]))
    if day_bits:
        text += " " + (" or ".join(day_bits) if len(day_bits) == 2 else day_bits[0])
    if mon not in ("*", "?"):
        text += " in " + _compress(mons, lambda v: MONTH_NAMES[v - 1])
    return text + "."


def next_cron_runs(expr, count=5, start=None):
    f, (mins, hours, doms, mons, dows) = _cron_parts(expr)
    start = (start or datetime.now()).replace(second=0, microsecond=0) + timedelta(minutes=1)
    dom_star, dow_star = f[2] in ("*", "?"), f[4] in ("*", "?")
    out, day = [], start.replace(hour=0, minute=0)
    for _ in range(366 * 6):
        if day.month in mons:
            dom_ok, dow_ok = day.day in doms, ((day.weekday() + 1) % 7) in dows
            if dom_star and dow_star:
                ok = True
            elif dom_star:
                ok = dow_ok
            elif dow_star:
                ok = dom_ok
            else:
                ok = dom_ok or dow_ok
            if ok:
                for h in sorted(hours):
                    for m in sorted(mins):
                        dt = day.replace(hour=h, minute=m)
                        if dt >= start:
                            out.append(dt)
                            if len(out) == count:
                                return out
        day += timedelta(days=1)
    return out


def humanize_delta(delta):
    s = max(0, int(delta.total_seconds()))
    d, s = divmod(s, 86400)
    h, s = divmod(s, 3600)
    m = s // 60
    parts = ([f"{d}d"] if d else []) + ([f"{h}h"] if h else []) + ([f"{m}m"] if m or not (d or h) else [])
    return "in " + " ".join(parts[:2])


# ======================================================================
#  PART 2 - LOOK & FEEL
# ======================================================================
IS_WIN = sys.platform.startswith("win")
IS_MAC = sys.platform == "darwin"
FONT = "Segoe UI" if IS_WIN else ("Helvetica Neue" if IS_MAC else "DejaVu Sans")
MONO = "Consolas" if IS_WIN else ("Menlo" if IS_MAC else "DejaVu Sans Mono")

C = dict(bg="#F1F5F9", side="#0F172A", side_hover="#1E293B", side_active="#27306B", card="#FFFFFF",
         text="#0F172A", muted="#64748B", border="#E2E8F0", accent="#4F46E5", accent_dark="#4338CA",
         ok="#059669", err="#DC2626", side_text="#CBD5E1", side_muted="#64748B", out_bg="#F8FAFC")

TOOLS = [
    dict(key="json2java", title="JSON to Java", desc="Generate Java POJOs from JSON", icon="java", color="#F97316"),
    dict(key="json2ts", title="JSON to TypeScript", desc="Generate TypeScript interfaces and types",
         icon="ts", color="#2563EB"),
    dict(key="xml2json", title="XML to JSON", desc="Convert XML data into JSON", icon="xml", color="#0D9488"),
    dict(key="yaml2json", title="YAML to JSON", desc="Convert configuration files", icon="yaml", color="#7C3AED"),
    dict(key="sql2java", title="SQL to Java Models", desc="Generate Java entity classes from SQL tables",
         icon="sql", color="#DB2777"),
    dict(key="csv2json", title="CSV to JSON", desc="Convert spreadsheet data into JSON", icon="csv", color="#16A34A"),
    dict(key="base64", title="Base64 Encoder/Decoder", desc="Encode or decode text and files",
         icon="lock", color="#D97706"),
    dict(key="url", title="URL Encoder/Decoder", desc="Encode URLs and query parameters",
         icon="globe", color="#0891B2"),
    dict(key="regex", title="Regex Tester", desc="Test regular expressions against sample text",
         icon="regex", color="#E11D48"),
    dict(key="cron", title="Cron Expression Generator", desc="Create and explain scheduled job expressions",
         icon="clock", color="#4F46E5"),
]

SCALE = 1.0


def px(n):
    return max(1, int(round(n * SCALE)))


def round_rect(c, x1, y1, x2, y2, r, **kw):
    pts = [x1 + r, y1, x2 - r, y1, x2, y1, x2, y1 + r, x2, y2 - r, x2, y2, x2 - r, y2,
           x1 + r, y2, x1, y2, x1, y2 - r, x1, y1 + r, x1, y1]
    return c.create_polygon(pts, smooth=True, **kw)


def draw_icon(c, kind, x, y, size, color):
    """Draws a rounded badge with a white pictogram. Works on any Tk canvas."""
    s = size / 48.0
    w = max(2, int(round(2.6 * s)))
    white = "#FFFFFF"

    def P(*pts):
        return [(x + a * s) if i % 2 == 0 else (y + a * s) for i, a in enumerate(pts)]

    def line(*pts, width=None, smooth=False):
        c.create_line(*P(*pts), fill=white, width=width or w, capstyle="round", joinstyle="round", smooth=smooth)

    def arc(x1, y1, x2, y2, start, extent):
        c.create_arc(*P(x1, y1, x2, y2), start=start, extent=extent, style="arc", outline=white, width=w)

    def oval(x1, y1, x2, y2, fill=""):
        c.create_oval(*P(x1, y1, x2, y2), outline=white, width=w, fill=fill)

    round_rect(c, x, y, x + size, y + size, size * 0.26, fill=color, outline=color)
    if kind == "java":  # coffee cup
        c.create_polygon(*P(13, 22, 33, 22, 30, 37, 16, 37), fill=white, outline=white)
        arc(28, 24, 38, 34, -90, 180)
        line(10, 40, 36, 40)
        for sx in (19, 24, 29):
            line(sx, 18, sx + 2, 14, sx, 10, width=max(1, w - 1), smooth=True)
    elif kind == "ts":
        c.create_text(x + size / 2, y + size / 2, text="TS", fill=white, font=(FONT, -int(size * 0.42), "bold"))
    elif kind == "xml":  # </>
        line(19, 16, 9, 24, 19, 32)
        line(29, 16, 39, 24, 29, 32)
        line(27, 13, 21, 35)
    elif kind == "yaml":  # document with lines
        c.create_polygon(*P(14, 8, 29, 8, 36, 15, 36, 40, 14, 40), outline=white, fill="", width=w)
        line(29, 8, 29, 15, 36, 15)
        line(19, 22, 31, 22)
        line(19, 28, 31, 28)
        line(19, 34, 26, 34)
    elif kind == "sql":  # database cylinder
        oval(12, 9, 36, 19)
        line(12, 14, 12, 34)
        line(36, 14, 36, 34)
        arc(12, 19, 36, 29, 180, 180)
        arc(12, 29, 36, 39, 180, 180)
    elif kind == "csv":  # table
        c.create_rectangle(*P(10, 12, 38, 36), outline=white, width=w)
        c.create_rectangle(*P(10, 12, 38, 20), outline=white, fill=white, width=w)
        line(10, 28, 38, 28)
        line(19.5, 12, 19.5, 36)
        line(28.5, 12, 28.5, 36)
    elif kind == "lock":  # padlock
        c.create_rectangle(*P(14, 23, 34, 39), fill=white, outline=white)
        arc(17, 10, 31, 32, 0, 180)
        line(17, 21, 17, 24)
        line(31, 21, 31, 24)
        c.create_oval(*P(22, 28, 26, 32), fill=color, outline=color)
        c.create_rectangle(*P(23.2, 31, 24.8, 35), fill=color, outline=color)
    elif kind == "globe":
        oval(10, 10, 38, 38)
        oval(18, 10, 30, 38)
        line(10, 24, 38, 24)
        line(12.5, 17, 35.5, 17, width=max(1, w - 1))
        line(12.5, 31, 35.5, 31, width=max(1, w - 1))
    elif kind == "regex":  # magnifier with asterisk
        oval(9, 9, 31, 31)
        line(27, 27, 39, 39, width=w + 1)
        thin = max(1, w - 1)
        line(20, 15, 20, 25, width=thin)
        line(15.7, 17.5, 24.3, 22.5, width=thin)
        line(15.7, 22.5, 24.3, 17.5, width=thin)
    elif kind == "clock":
        oval(9, 9, 39, 39)
        line(24, 24, 24, 14)
        line(24, 24, 31, 28)
        c.create_oval(*P(22, 22, 26, 26), fill=white, outline=white)
    elif kind == "home":
        c.create_polygon(*P(24, 9, 8, 24, 14, 24, 14, 38, 34, 38, 34, 24, 40, 24), fill=white, outline=white)
        c.create_rectangle(*P(20.5, 28, 27.5, 38), fill=color, outline=color)
    elif kind == "logo":
        c.create_text(x + size / 2, y + size / 2 - 1, text="{ }", fill=white, font=(FONT, -int(size * 0.46), "bold"))


class IconCanvas(tk.Canvas):
    def __init__(self, parent, kind, size, color, bg):
        s = px(size)
        super().__init__(parent, width=s, height=s, bg=bg, highlightthickness=0, bd=0)
        draw_icon(self, kind, 1, 1, s - 2, color)

    def set_bg(self, bg):
        self.configure(bg=bg)


def open_folder(path):
    try:
        if IS_WIN:
            os.startfile(path)
        elif IS_MAC:
            subprocess.run(["open", path])
        else:
            subprocess.run(["xdg-open", path])
    except Exception:
        pass


def bind_tree(widget, sequence, func):
    widget.bind(sequence, func, add="+")
    for child in widget.winfo_children():
        bind_tree(child, sequence, func)


# ---------------------------------------------------------------- widgets
class TextPane(tk.Frame):
    """A titled text box with Open / Paste / Clear / Copy / Save buttons."""

    def __init__(self, parent, title, kind="input", sample=None, on_change=None):
        super().__init__(parent, bg=C["card"], highlightbackground=C["border"], highlightthickness=1)
        self.on_change = on_change
        self.sample = sample
        head = tk.Frame(self, bg=C["card"])
        head.pack(fill="x", padx=12, pady=(8, 2))
        tk.Label(head, text=title.upper(), bg=C["card"], fg=C["muted"], font=(FONT, 9, "bold")).pack(side="left")
        btns = tk.Frame(head, bg=C["card"])
        btns.pack(side="right")
        specs = [("Copy", self.copy), ("Save...", self.save_file)] if kind == "output" else \
            ([("Sample", self.load_sample)] if sample else []) + \
            [("Open...", self.open_file), ("Paste", self.paste), ("Clear", self.clear)]
        for label, cmd in specs:
            ttk.Button(btns, text=label, command=cmd, style="Mini.TButton").pack(side="left", padx=(2, 0))
        self.count = tk.Label(head, text="", bg=C["card"], fg=C["muted"], font=(FONT, 8))
        self.count.pack(side="right", padx=10)

        body = tk.Frame(self, bg=C["card"])
        body.pack(fill="both", expand=True, padx=1, pady=(0, 1))
        bg = C["out_bg"] if kind == "output" else C["card"]
        self.text = tk.Text(body, wrap="none", font=(MONO, 10), undo=True, relief="flat", bd=0, padx=12, pady=8,
                            bg=bg, fg=C["text"], insertbackground=C["text"], selectbackground="#C7D2FE",
                            selectforeground=C["text"], highlightthickness=0)
        vs = ttk.Scrollbar(body, orient="vertical", command=self.text.yview)
        hs = ttk.Scrollbar(body, orient="horizontal", command=self.text.xview)
        self.text.configure(yscrollcommand=vs.set, xscrollcommand=hs.set)
        self.text.grid(row=0, column=0, sticky="nsew")
        vs.grid(row=0, column=1, sticky="ns")
        hs.grid(row=1, column=0, sticky="ew")
        body.rowconfigure(0, weight=1)
        body.columnconfigure(0, weight=1)
        self.text.bind("<KeyRelease>", lambda e: self._changed())
        self.text.bind("<<Paste>>", lambda e: self.after(50, self._changed))
        self.text.bind("<<Cut>>", lambda e: self.after(50, self._changed))
        self.text.bind("<Control-Return>", lambda e: (self.winfo_toplevel().run_primary(), "break")[1])

    def _changed(self):
        s = self.get()
        self.count.config(text=f"{len(s):,} chars  |  {s.count(chr(10)) + 1 if s else 0} lines")
        if self.on_change:
            self.on_change()

    def get(self):
        return self.text.get("1.0", "end-1c")

    def set(self, s):
        self.text.delete("1.0", "end")
        self.text.insert("1.0", s)
        self._changed()

    def clear(self):
        self.set("")

    def load_sample(self):
        self.set(self.sample)

    def copy(self):
        s = self.get()
        if s:
            self.clipboard_clear()
            self.clipboard_append(s)
            self.winfo_toplevel().set_status("Copied to the clipboard")

    def paste(self):
        try:
            self.set(self.clipboard_get())
        except tk.TclError:
            self.winfo_toplevel().set_status("The clipboard is empty", True)

    def open_file(self):
        path = filedialog.askopenfilename(title="Open a text file")
        if path:
            try:
                self.set(read_text_file(path))
                self.winfo_toplevel().set_status(f"Opened {os.path.basename(path)}")
            except OSError as e:
                self.winfo_toplevel().set_status(f"Could not open the file: {e}", True)

    def save_file(self):
        s = self.get()
        if not s:
            return self.winfo_toplevel().set_status("Nothing to save yet", True)
        path = filedialog.asksaveasfilename(title="Save output", defaultextension=".txt")
        if path:
            with open(path, "w", encoding="utf-8", newline="") as fh:
                fh.write(s)
            self.winfo_toplevel().set_status(f"Saved {path}")


class Choice:
    """Combobox value holder."""

    def __init__(self, var, values):
        self.var, self.values = var, values

    def get(self):
        return self.var.get()

    def index(self):
        return self.values.index(self.var.get())


class OptionBar(tk.Frame):
    def __init__(self, parent):
        super().__init__(parent, bg=C["card"], highlightbackground=C["border"], highlightthickness=1)
        self.top = tk.Frame(self, bg=C["card"])
        self.top.pack(fill="x", padx=12, pady=10)
        self.cur = tk.Frame(self.top, bg=C["card"])
        self.cur.pack(side="left")
        self.buttons = tk.Frame(self.top, bg=C["card"])
        self.buttons.pack(side="right")

    def row(self):
        self.cur = tk.Frame(self, bg=C["card"])
        self.cur.pack(fill="x", padx=12, pady=(0, 10))

    def _label(self, text):
        tk.Label(self.cur, text=text, bg=C["card"], fg=C["muted"], font=(FONT, 9)).pack(side="left", padx=(0, 6))

    def entry(self, label, default, width=14):
        self._label(label)
        var = tk.StringVar(value=default)
        ttk.Entry(self.cur, textvariable=var, width=width).pack(side="left", padx=(0, 18))
        return var

    def combo(self, label, values, index=0, width=18):
        self._label(label)
        var = tk.StringVar()
        cb = ttk.Combobox(self.cur, textvariable=var, values=values, state="readonly", width=width)
        cb.current(index)
        cb.pack(side="left", padx=(0, 18))
        return Choice(var, values)

    def check(self, label, default=True):
        var = tk.BooleanVar(value=default)
        ttk.Checkbutton(self.cur, text=label, variable=var, style="Card.TCheckbutton").pack(side="left", padx=(0, 18))
        return var

    def button(self, text, command, primary=False):
        ttk.Button(self.buttons, text=text, command=command,
                   style="Accent.TButton" if primary else "Soft.TButton").pack(side="left", padx=(8, 0))


class NavItem(tk.Frame):
    def __init__(self, parent, title, icon, color, command):
        super().__init__(parent, bg=C["side"], cursor="hand2")
        self.active = False
        self.ind = tk.Frame(self, width=4, bg=C["side"])
        self.ind.pack(side="left", fill="y")
        self.icon = IconCanvas(self, icon, 30, color, C["side"])
        self.icon.pack(side="left", padx=(14, 12), pady=6)
        self.label = tk.Label(self, text=title, bg=C["side"], fg=C["side_text"], font=(FONT, 10), anchor="w")
        self.label.pack(side="left", fill="x", expand=True)
        for seq, fn in (("<Enter>", lambda e: self.paint(True)), ("<Leave>", lambda e: self.paint(False)),
                        ("<Button-1>", lambda e: command())):
            bind_tree(self, seq, fn)

    def paint(self, hover=False):
        bg = C["side_active"] if self.active else (C["side_hover"] if hover else C["side"])
        for w in (self, self.label):
            w.configure(bg=bg)
        self.icon.set_bg(bg)
        self.ind.configure(bg=C["accent"] if self.active else bg)
        self.label.configure(fg="#FFFFFF" if self.active else C["side_text"],
                             font=(FONT, 10, "bold") if self.active else (FONT, 10))

    def set_active(self, active):
        self.active = active
        self.paint(False)


class ToolCard(tk.Frame):
    def __init__(self, parent, number, tool, command):
        super().__init__(parent, bg=C["card"], highlightbackground=C["border"], highlightthickness=1,
                         cursor="hand2")
        top = tk.Frame(self, bg=C["card"])
        top.pack(fill="x", padx=16, pady=(16, 0))
        IconCanvas(top, tool["icon"], 56, tool["color"], C["card"]).pack(side="left")
        tk.Label(top, text=f"{number:02d}", fg="#CBD5E1", bg=C["card"], font=(FONT, 16, "bold")).pack(
            side="right", anchor="n")
        tk.Label(self, text=tool["title"], font=(FONT, 12, "bold"), fg=C["text"], bg=C["card"], anchor="w",
                 justify="left", wraplength=px(165)).pack(fill="x", padx=16, pady=(14, 2))
        tk.Label(self, text=tool["desc"], font=(FONT, 9), fg=C["muted"], bg=C["card"], anchor="w",
                 justify="left", wraplength=px(165)).pack(fill="x", padx=16, pady=(0, 6))
        tk.Label(self, text="Open  >", font=(FONT, 9, "bold"), fg=tool["color"], bg=C["card"],
                 anchor="w").pack(fill="x", padx=16, pady=(4, 16))
        bind_tree(self, "<Enter>", lambda e: self.configure(highlightbackground=tool["color"]))
        bind_tree(self, "<Leave>", lambda e: self.configure(highlightbackground=C["border"]))
        bind_tree(self, "<Button-1>", lambda e: command())


# ======================================================================
#  PART 3 - PAGES
# ======================================================================
class ToolPage(tk.Frame):
    def __init__(self, app, tool):
        super().__init__(app.content, bg=C["bg"])
        self.app, self.tool = app, tool
        head = tk.Frame(self, bg=C["bg"])
        head.pack(fill="x", padx=24, pady=(20, 14))
        IconCanvas(head, tool["icon"], 52, tool["color"], C["bg"]).pack(side="left")
        txt = tk.Frame(head, bg=C["bg"])
        txt.pack(side="left", padx=14)
        tk.Label(txt, text=tool["title"], font=(FONT, 18, "bold"), fg=C["text"], bg=C["bg"]).pack(anchor="w")
        tk.Label(txt, text=tool["desc"], font=(FONT, 10), fg=C["muted"], bg=C["bg"]).pack(anchor="w")
        self.body = tk.Frame(self, bg=C["bg"])
        self.body.pack(fill="both", expand=True, padx=24, pady=(0, 16))
        self.build()

    def build(self):
        raise NotImplementedError

    def primary(self):
        pass

    def status(self, msg, error=False):
        self.app.set_status(msg, error)


class ConverterPage(ToolPage):
    """Input box -> option bar -> output box."""
    in_title, out_title, sample = "Input", "Output", None

    def build(self):
        self.bar = OptionBar(self.body)
        self.bar.pack(fill="x", pady=(0, 12))
        self.options(self.bar)
        for label, fn, primary in self.actions():
            self.bar.button(label, fn, primary)
        panes = tk.Frame(self.body, bg=C["bg"])
        panes.pack(fill="both", expand=True)
        panes.columnconfigure((0, 1), weight=1, uniform="pane")
        panes.rowconfigure(0, weight=1)
        self.inp = TextPane(panes, self.in_title, "input", self.sample)
        self.out = TextPane(panes, self.out_title, "output")
        self.inp.grid(row=0, column=0, sticky="nsew", padx=(0, 6))
        self.out.grid(row=0, column=1, sticky="nsew", padx=(6, 0))
        if self.sample:
            self.inp.set(self.sample)

    def options(self, bar):
        pass

    def actions(self):
        return [("Convert", self.convert, True)]

    def primary(self):
        self.convert()

    def text_in(self):
        s = self.inp.get()
        if not s.strip():
            raise ValueError("Paste, type or open some input first.")
        return s

    def apply(self, work):
        try:
            out, msg = work()
        except json.JSONDecodeError as e:
            return self.status(f"Invalid JSON: {e.msg} (line {e.lineno}, column {e.colno})", True)
        except Exception as e:
            return self.status(str(e) or type(e).__name__, True)
        self.out.set(out)
        self.status(msg)

    def convert(self):
        raise NotImplementedError


class FilesExportMixin:
    """Pages that generate several .java files can also write them to a folder."""
    files = None

    def show_files(self, files):
        self.files = files
        return "\n\n".join(f"// ===== {name} =====\n{code}" for name, code in files), \
            f"Generated {len(files)} class{'es' if len(files) != 1 else ''} - use 'Export .java files...' to save them"

    def export(self):
        self.files = None
        self.convert()
        if not self.files:
            return
        folder = filedialog.askdirectory(title="Export .java files to...")
        if not folder:
            return
        for name, code in self.files:
            with open(os.path.join(folder, name), "w", encoding="utf-8", newline="\n") as fh:
                fh.write(code)
        self.status(f"Saved {len(self.files)} file(s) to {folder}")
        open_folder(folder)


JSON_SAMPLE = """{
  "id": 101,
  "user_name": "Asha",
  "active": true,
  "balance": 1520.75,
  "address": { "street": "12 Main Street", "city": "Springfield", "zip": "10001" },
  "orders": [
    { "order_id": 1, "total": 250.5, "items": ["pen", "book"] },
    { "order_id": 2, "total": 99, "coupon": null }
  ]
}"""


class JsonToJavaPage(FilesExportMixin, ConverterPage):
    in_title, out_title, sample = "JSON input", "Java output", JSON_SAMPLE

    def options(self, bar):
        self.root_name = bar.entry("Root class", "Root", 10)
        self.package = bar.entry("Package", "com.example.model", 20)
        self.style = bar.combo("Style", ["Getters & setters", "Lombok @Data", "Java record"], 0, 16)
        bar.row()
        self.jackson = bar.check("Add Jackson @JsonProperty when names differ", True)

    def actions(self):
        return [("Export .java files...", self.export, False), ("Convert", self.convert, True)]

    def convert(self):
        self.apply(lambda: self.show_files(json_to_java(
            self.text_in(), self.root_name.get(), self.package.get(), self.style.index(), self.jackson.get())))


class JsonToTsPage(ConverterPage):
    in_title, out_title, sample = "JSON input", "TypeScript output", JSON_SAMPLE

    def options(self, bar):
        self.root_name = bar.entry("Root type", "Root", 12)
        self.kind = bar.combo("Declare as", ["interface", "type alias"], 0, 12)
        self.export = bar.check("export", True)

    def convert(self):
        def work():
            out = json_to_typescript(self.text_in(), self.root_name.get(),
                                     "interface" if self.kind.index() == 0 else "type", self.export.get())
            return out, f"Generated {out.count('{') } type(s)"
        self.apply(work)


XML_SAMPLE = """<?xml version="1.0" encoding="UTF-8"?>
<library name="City Library">
  <book id="1" available="true">
    <title>Clean Code</title>
    <author>Robert C. Martin</author>
    <price>33.50</price>
  </book>
  <book id="2" available="false">
    <title>Refactoring</title>
    <author>Martin Fowler</author>
    <price>45</price>
  </book>
</library>"""

INDENTS = ["2 spaces", "4 spaces", "Compact"]


def _indent(choice):
    return (2, 4, None)[choice.index()]


class XmlToJsonPage(ConverterPage):
    in_title, out_title, sample = "XML input", "JSON output", XML_SAMPLE

    def options(self, bar):
        self.indent = bar.combo("Indent", INDENTS, 0, 10)
        self.attrs = bar.check("Include attributes (@name)", True)
        self.detect = bar.check("Detect numbers & booleans", False)

    def convert(self):
        self.apply(lambda: (xml_to_json(self.text_in(), _indent(self.indent), self.attrs.get(), self.detect.get()),
                            "Converted XML to JSON"))


YAML_SAMPLE = """# application config
app:
  name: demo-service
  version: 1.4
  debug: false
server:
  host: localhost
  ports: [8080, 8443]
database:
  url: "jdbc:postgresql://localhost:5432/demo"
  pool: { min: 2, max: 10 }
features:
  - name: search
    enabled: true
  - name: export
    enabled: false
"""


class YamlToJsonPage(ConverterPage):
    in_title, out_title, sample = "YAML input", "JSON output", YAML_SAMPLE

    def options(self, bar):
        self.indent = bar.combo("Indent", INDENTS, 0, 10)

    def convert(self):
        def work():
            out, builtin = yaml_to_json(self.text_in(), _indent(self.indent))
            return out, "Converted YAML to JSON" + (" (built-in parser - pip install pyyaml for full YAML)"
                                                    if builtin else "")
        self.apply(work)


SQL_SAMPLE = """CREATE TABLE users (
  id BIGINT AUTO_INCREMENT PRIMARY KEY,
  user_name VARCHAR(100) NOT NULL,
  email VARCHAR(255),
  is_active BOOLEAN DEFAULT TRUE,
  balance DECIMAL(10, 2),
  created_at TIMESTAMP NOT NULL
);

CREATE TABLE order_items (
  id INT PRIMARY KEY AUTO_INCREMENT,
  order_id BIGINT NOT NULL,
  product_name VARCHAR(80) NOT NULL,
  quantity INT NOT NULL,
  unit_price NUMERIC(8, 2) NOT NULL,
  shipped_on DATE
);"""


class SqlToJavaPage(FilesExportMixin, ConverterPage):
    in_title, out_title, sample = "SQL (CREATE TABLE)", "Java entities", SQL_SAMPLE

    def options(self, bar):
        self.package = bar.entry("Package", "com.example.entity", 20)
        self.ns = bar.combo("JPA package", ["jakarta.persistence", "javax.persistence"], 0, 18)
        bar.row()
        self.jpa = bar.check("JPA annotations (@Entity, @Id, @Column)", True)
        self.lombok = bar.check("Lombok @Data instead of getters/setters", False)

    def actions(self):
        return [("Export .java files...", self.export, False), ("Convert", self.convert, True)]

    def convert(self):
        self.apply(lambda: self.show_files(sql_to_java(
            self.text_in(), self.package.get(), self.jpa.get(), self.ns.get(), self.lombok.get())))


CSV_SAMPLE = """name,age,city,member
Asha,29,Springfield,true
Ravi,34,Shelbyville,false
Maya,41,"Ogden, UT",true
"""


class CsvToJsonPage(ConverterPage):
    in_title, out_title, sample = "CSV input", "JSON output", CSV_SAMPLE
    DELIMS = ["Auto-detect", "Comma ,", "Semicolon ;", "Tab", "Pipe |"]

    def options(self, bar):
        self.delim = bar.combo("Delimiter", self.DELIMS, 0, 12)
        self.indent = bar.combo("Indent", INDENTS, 0, 10)
        bar.row()
        self.header = bar.check("First row is a header", True)
        self.detect = bar.check("Detect numbers, booleans and empty cells", True)

    def convert(self):
        def work():
            d = ("auto", ",", ";", "\t", "|")[self.delim.index()]
            out, used, n = csv_to_json(self.text_in(), d, self.header.get(), self.detect.get(), _indent(self.indent))
            name = {",": "comma", ";": "semicolon", "\t": "tab", "|": "pipe"}.get(used, repr(used))
            return out, f"Converted {n} row(s) (delimiter: {name})"
        self.apply(work)


class Base64Page(ConverterPage):
    in_title, out_title, sample = "Text input", "Result", "Hello, DevToolkit!"

    def options(self, bar):
        self.urlsafe = bar.check("URL-safe alphabet (- and _)", False)

    def actions(self):
        return [("Encode file...", self.encode_file, False), ("Decode to file...", self.decode_file, False),
                ("Decode", self.decode, False), ("Encode", self.encode, True)]

    def primary(self):
        self.encode()

    def encode(self):
        self.apply(lambda: (b64_encode(self.text_in().encode("utf-8"), self.urlsafe.get()), "Encoded to Base64"))

    def decode(self):
        self.apply(lambda: (b64_decode_text(self.text_in(), self.urlsafe.get()), "Decoded from Base64"))

    def encode_file(self):
        path = filedialog.askopenfilename(title="Choose a file to encode")
        if not path:
            return
        try:
            with open(path, "rb") as fh:
                enc = b64_encode(fh.read(), self.urlsafe.get())
            target = filedialog.asksaveasfilename(title="Save the Base64 text as",
                                                  initialfile=os.path.basename(path) + ".b64.txt")
            if target:
                with open(target, "w", encoding="ascii") as fh:
                    fh.write(enc)
            self.out.set(enc if len(enc) <= 200000 else enc[:2000] + f"\n... ({len(enc):,} characters in total)")
            self.status(f"Encoded {os.path.basename(path)} ({len(enc):,} characters)" +
                        (f" - saved to {target}" if target else ""))
        except OSError as e:
            self.status(f"File error: {e}", True)

    def decode_file(self):
        try:
            raw = b64_decode_bytes(self.text_in(), self.urlsafe.get())
        except ValueError as e:
            return self.status(str(e), True)
        target = filedialog.asksaveasfilename(title="Save the decoded file as")
        if target:
            with open(target, "wb") as fh:
                fh.write(raw)
            self.status(f"Saved {len(raw):,} bytes to {target}")


class UrlPage(ConverterPage):
    in_title, out_title = "Input", "Result"
    sample = "https://example.com/search?q=hello world&lang=en&tags=a,b#top"

    def options(self, bar):
        self.mode = bar.combo("Mode", URL_MODES, 0, 28)

    def actions(self):
        return [("Parse URL", self.parse, False), ("Decode", self.decode, False), ("Encode", self.encode, True)]

    def primary(self):
        self.encode()

    def encode(self):
        self.apply(lambda: (url_encode(self.text_in(), self.mode.index()), "URL-encoded"))

    def decode(self):
        self.apply(lambda: (url_decode(self.text_in().strip(), self.mode.index()), "URL-decoded"))

    def parse(self):
        self.apply(lambda: (url_parse(self.text_in()), "Parsed the URL"))


class RegexPage(ToolPage):
    SAMPLE_TEXT = ("Contact: alice@example.com, bob@test.org\nSupport: help@company.io\n"
                   "Call 555-0134 or 555-0199 for details.")

    def build(self):
        self._job = None
        self.matches = []
        card = tk.Frame(self.body, bg=C["card"], highlightbackground=C["border"], highlightthickness=1)
        card.pack(fill="x", pady=(0, 12))
        row = tk.Frame(card, bg=C["card"])
        row.pack(fill="x", padx=12, pady=(10, 4))
        tk.Label(row, text="Pattern", bg=C["card"], fg=C["muted"], font=(FONT, 9)).pack(side="left", padx=(0, 8))
        self.pattern = tk.StringVar(value=r"[\w.]+@[\w.]+\.\w+")
        ttk.Entry(row, textvariable=self.pattern, font=(MONO, 11)).pack(side="left", fill="x", expand=True)
        flags = tk.Frame(card, bg=C["card"])
        flags.pack(fill="x", padx=12, pady=(0, 8))
        self.flag_vars = {}
        for key, label in (("i", "Ignore case (i)"), ("m", "Multiline (m)"), ("s", "Dot matches newline (s)"),
                           ("x", "Verbose (x)")):
            var = tk.BooleanVar(value=False)
            self.flag_vars[key] = var
            ttk.Checkbutton(flags, text=label, variable=var, style="Card.TCheckbutton",
                            command=self.refresh).pack(side="left", padx=(0, 16))
        tk.Label(flags, text="Uses Python's regex engine", bg=C["card"], fg=C["muted"], font=(FONT, 8)).pack(
            side="right")
        self.pattern.trace_add("write", lambda *a: self.schedule())

        cols = tk.Frame(self.body, bg=C["bg"])
        cols.pack(fill="both", expand=True)
        cols.columnconfigure((0, 1), weight=1, uniform="rx")
        cols.rowconfigure(0, weight=1)
        self.source = TextPane(cols, "Test text", "input", self.SAMPLE_TEXT, on_change=self.schedule)
        self.source.grid(row=0, column=0, sticky="nsew", padx=(0, 6))
        self.source.set(self.SAMPLE_TEXT)
        t = self.source.text
        t.tag_configure("m0", background="#C7D2FE")
        t.tag_configure("m1", background="#A5F3FC")
        t.tag_configure("cur", background="#FDE047")

        right = tk.Frame(cols, bg=C["card"], highlightbackground=C["border"], highlightthickness=1)
        right.grid(row=0, column=1, sticky="nsew", padx=(6, 0))
        self.summary = tk.Label(right, text="", bg=C["card"], fg=C["muted"], font=(FONT, 10, "bold"), anchor="w")
        self.summary.pack(fill="x", padx=12, pady=(10, 6))
        self.tree = ttk.Treeview(right, columns=("n", "match", "span", "groups"), show="headings", height=8)
        for col, label, width, stretch in (("n", "#", 40, False), ("match", "Match", 190, True),
                                           ("span", "Position", 80, False), ("groups", "Groups", 190, True)):
            self.tree.heading(col, text=label)
            self.tree.column(col, width=width, stretch=stretch, anchor="w")
        self.tree.pack(fill="both", expand=True, padx=12)
        self.tree.bind("<<TreeviewSelect>>", self.on_select)
        rep = tk.Frame(right, bg=C["card"])
        rep.pack(fill="x", padx=12, pady=(10, 4))
        tk.Label(rep, text="Replace with", bg=C["card"], fg=C["muted"], font=(FONT, 9)).pack(side="left", padx=(0, 8))
        self.repl = tk.StringVar()
        ttk.Entry(rep, textvariable=self.repl, font=(MONO, 10)).pack(side="left", fill="x", expand=True)
        self.repl.trace_add("write", lambda *a: self.schedule())
        self.repl_out = tk.Text(right, height=4, wrap="word", font=(MONO, 10), relief="flat", bd=0, padx=10, pady=6,
                                bg=C["out_bg"], fg=C["text"], highlightthickness=0)
        self.repl_out.pack(fill="x", padx=12, pady=(0, 12))
        self.refresh()

    def schedule(self):
        if self._job:
            self.after_cancel(self._job)
        self._job = self.after(250, self.refresh)

    def refresh(self):
        self._job = None
        t = self.source.text
        for tag in ("m0", "m1", "cur"):
            t.tag_remove(tag, "1.0", "end")
        self.tree.delete(*self.tree.get_children())
        self.matches = []
        self.repl_out.delete("1.0", "end")
        pat = self.pattern.get()
        if not pat:
            return self.summary.config(text="Type a pattern above to start matching.", fg=C["muted"])
        flags = regex_flags(**{k: v.get() for k, v in self.flag_vars.items()})
        try:
            rx = re.compile(pat, flags)
        except re.error as e:
            return self.summary.config(text=f"Invalid pattern: {e}", fg=C["err"])
        text = self.source.get()
        names = {i: n for n, i in rx.groupindex.items()}
        truncated = False
        for count, m in enumerate(rx.finditer(text)):
            if count >= 1000:
                truncated = True
                break
            self.matches.append(m)
            if m.end() > m.start():
                t.tag_add(f"m{count % 2}", f"1.0+{m.start()}c", f"1.0+{m.end()}c")
            groups = ", ".join(f"{names.get(i, i)}={g!r}" for i, g in enumerate(m.groups(), 1))
            shown = m.group(0).replace("\n", "\\n")
            self.tree.insert("", "end", iid=str(count), values=(count + 1, shown, f"{m.start()}-{m.end()}", groups))
        n = len(self.matches)
        self.summary.config(text=f"{n}{'+' if truncated else ''} match{'es' if n != 1 else ''}"
                            + (" (showing the first 1000)" if truncated else ""),
                            fg=C["ok"] if n else C["muted"])
        if self.repl.get() != "":
            try:
                self.repl_out.insert("1.0", rx.sub(self.repl.get(), text))
            except (re.error, IndexError) as e:
                self.repl_out.insert("1.0", f"Replacement error: {e}")

    def on_select(self, _event=None):
        sel = self.tree.selection()
        if not sel:
            return
        m = self.matches[int(sel[0])]
        t = self.source.text
        t.tag_remove("cur", "1.0", "end")
        if m.end() > m.start():
            t.tag_add("cur", f"1.0+{m.start()}c", f"1.0+{m.end()}c")
            t.tag_raise("cur")
            t.see(f"1.0+{m.start()}c")


class CronPage(ToolPage):
    def build(self):
        self._sync = False
        card = tk.Frame(self.body, bg=C["card"], highlightbackground=C["border"], highlightthickness=1)
        card.pack(fill="x", pady=(0, 12))
        tk.Label(card, text="CRON EXPRESSION", bg=C["card"], fg=C["muted"], font=(FONT, 9, "bold")).pack(
            anchor="w", padx=14, pady=(10, 2))
        row = tk.Frame(card, bg=C["card"])
        row.pack(fill="x", padx=14)
        self.expr = tk.StringVar(value="0 9 * * 1-5")
        ttk.Entry(row, textvariable=self.expr, font=(MONO, 18)).pack(side="left", fill="x", expand=True)
        ttk.Button(row, text="Copy", style="Accent.TButton", command=self.copy).pack(side="left", padx=(10, 0))

        fields = tk.Frame(card, bg=C["card"])
        fields.pack(fill="x", padx=14, pady=(12, 4))
        self.vars = []
        for i, (name, _lo, _hi, _names, hint) in enumerate(CRON_FIELDS):
            col = tk.Frame(fields, bg=C["card"])
            col.pack(side="left", padx=(0, 14))
            tk.Label(col, text=name, bg=C["card"], fg=C["text"], font=(FONT, 9, "bold")).pack(anchor="w")
            var = tk.StringVar()
            ttk.Entry(col, textvariable=var, width=10, font=(MONO, 12), justify="center").pack(anchor="w", pady=2)
            tk.Label(col, text=hint, bg=C["card"], fg=C["muted"], font=(FONT, 8)).pack(anchor="w")
            var.trace_add("write", lambda *a: self.fields_changed())
            self.vars.append(var)
        tk.Label(card, text="Symbols:  *  any value     ,  list (1,15)     -  range (1-5)     /  step (*/10)",
                 bg=C["card"], fg=C["muted"], font=(FONT, 9)).pack(anchor="w", padx=14, pady=(6, 4))

        chips = tk.Frame(card, bg=C["card"])
        chips.pack(fill="x", padx=14, pady=(2, 12))
        tk.Label(chips, text="Presets", bg=C["card"], fg=C["muted"], font=(FONT, 9)).grid(row=0, column=0,
                                                                                         padx=(0, 8), sticky="w")
        for i, (label, value) in enumerate(CRON_PRESETS):
            ttk.Button(chips, text=label, style="Soft.TButton",
                       command=lambda v=value: self.expr.set(v)).grid(row=i // 5, column=1 + i % 5, padx=3, pady=3,
                                                                       sticky="w")

        lower = tk.Frame(self.body, bg=C["bg"])
        lower.pack(fill="both", expand=True)
        lower.columnconfigure((0, 1), weight=1, uniform="cr")
        lower.rowconfigure(0, weight=1)
        left = tk.Frame(lower, bg=C["card"], highlightbackground=C["border"], highlightthickness=1)
        left.grid(row=0, column=0, sticky="nsew", padx=(0, 6))
        tk.Label(left, text="WHAT IT MEANS", bg=C["card"], fg=C["muted"], font=(FONT, 9, "bold")).pack(
            anchor="w", padx=14, pady=(10, 6))
        self.explain = tk.Label(left, text="", bg=C["card"], fg=C["text"], font=(FONT, 15), justify="left",
                                wraplength=px(430), anchor="nw")
        self.explain.pack(fill="x", padx=14)
        right = tk.Frame(lower, bg=C["card"], highlightbackground=C["border"], highlightthickness=1)
        right.grid(row=0, column=1, sticky="nsew", padx=(6, 0))
        tk.Label(right, text="NEXT 5 RUNS (YOUR LOCAL TIME)", bg=C["card"], fg=C["muted"],
                 font=(FONT, 9, "bold")).pack(anchor="w", padx=14, pady=(10, 6))
        self.runs = tk.Frame(right, bg=C["card"])
        self.runs.pack(fill="x", padx=14)
        self.expr.trace_add("write", lambda *a: self.expr_changed())
        self.expr_changed()

    def primary(self):
        self.copy()

    def copy(self):
        self.clipboard_clear()
        self.clipboard_append(self.expr.get().strip())
        self.status("Cron expression copied")

    def expr_changed(self):
        if not self._sync:
            parts = self.expr.get().split()
            if len(parts) == 5:
                self._sync = True
                for var, part in zip(self.vars, parts):
                    var.set(part)
                self._sync = False
        self.refresh()

    def fields_changed(self):
        if self._sync:
            return
        self._sync = True
        self.expr.set(" ".join((v.get().strip() or "*") for v in self.vars))
        self._sync = False
        self.refresh()

    def refresh(self):
        for w in self.runs.winfo_children():
            w.destroy()
        try:
            text = describe_cron(self.expr.get())
            runs = next_cron_runs(self.expr.get(), 5)
        except ValueError as e:
            self.explain.config(text=str(e), fg=C["err"], font=(FONT, 11))
            return
        self.explain.config(text=text, fg=C["text"], font=(FONT, 15))
        now = datetime.now()
        if not runs:
            tk.Label(self.runs, text="This schedule never runs (for example, Feb 30).", bg=C["card"],
                     fg=C["err"], font=(FONT, 10)).pack(anchor="w")
        for i, dt in enumerate(runs, 1):
            line = tk.Frame(self.runs, bg=C["card"])
            line.pack(fill="x", pady=3)
            tk.Label(line, text=str(i), width=2, bg="#EEF2FF", fg=C["accent"], font=(FONT, 9, "bold")).pack(
                side="left")
            tk.Label(line, text=dt.strftime("%a, %d %b %Y   %H:%M"), bg=C["card"], fg=C["text"],
                     font=(MONO, 11)).pack(side="left", padx=10)
            tk.Label(line, text=humanize_delta(dt - now), bg=C["card"], fg=C["muted"], font=(FONT, 9)).pack(
                side="left")


PAGES = {"json2java": JsonToJavaPage, "json2ts": JsonToTsPage, "xml2json": XmlToJsonPage,
         "yaml2json": YamlToJsonPage, "sql2java": SqlToJavaPage, "csv2json": CsvToJsonPage,
         "base64": Base64Page, "url": UrlPage, "regex": RegexPage, "cron": CronPage}


# ======================================================================
#  PART 4 - MAIN WINDOW
# ======================================================================
LOGO_PNG = ""  # optional embedded window icon (base64 PNG), filled in below


class App(tk.Tk):
    def __init__(self):
        super().__init__()
        global SCALE
        SCALE = max(1.0, float(self.tk.call("tk", "scaling")) / (96 / 72))
        self.title("DevToolkit - developer utilities")
        self.geometry(f"{px(1280)}x{px(800)}")
        self.minsize(px(1100), px(700))
        self.configure(bg=C["bg"])
        if LOGO_PNG:
            try:
                self.iconphoto(True, tk.PhotoImage(data=LOGO_PNG))
            except tk.TclError:
                pass
        self.setup_style()

        self.sidebar = tk.Frame(self, bg=C["side"], width=px(250))
        self.sidebar.pack(side="left", fill="y")
        self.sidebar.pack_propagate(False)
        right = tk.Frame(self, bg=C["bg"])
        right.pack(side="left", fill="both", expand=True)
        statusbar = tk.Frame(right, bg=C["card"], highlightbackground=C["border"], highlightthickness=1)
        statusbar.pack(side="bottom", fill="x")
        self.status_label = tk.Label(statusbar, text="Ready", bg=C["card"], fg=C["muted"], font=(FONT, 9),
                                     anchor="w")
        self.status_label.pack(side="left", padx=14, pady=5)
        tk.Label(statusbar, text="Ctrl+Enter = run   |   all processing stays on this computer", bg=C["card"],
                 fg=C["muted"], font=(FONT, 8)).pack(side="right", padx=14)
        self.content = tk.Frame(right, bg=C["bg"])
        self.content.pack(fill="both", expand=True)

        brand = tk.Frame(self.sidebar, bg=C["side"])
        brand.pack(fill="x", padx=16, pady=(20, 16))
        IconCanvas(brand, "logo", 40, C["accent"], C["side"]).pack(side="left")
        names = tk.Frame(brand, bg=C["side"])
        names.pack(side="left", padx=12)
        tk.Label(names, text="DevToolkit", bg=C["side"], fg="#FFFFFF", font=(FONT, 14, "bold")).pack(anchor="w")
        tk.Label(names, text="Developer utilities", bg=C["side"], fg=C["side_muted"], font=(FONT, 9)).pack(anchor="w")

        self.nav, self.pages, self.current = {}, {}, None
        self.nav["home"] = NavItem(self.sidebar, "Home", "home", C["accent"], lambda: self.show("home"))
        self.nav["home"].pack(fill="x")
        tk.Label(self.sidebar, text="TOOLS", bg=C["side"], fg=C["side_muted"], font=(FONT, 8, "bold"),
                 anchor="w").pack(fill="x", padx=20, pady=(14, 4))
        for tool in TOOLS:
            item = NavItem(self.sidebar, tool["title"], tool["icon"], tool["color"],
                           lambda k=tool["key"]: self.show(k))
            item.pack(fill="x")
            self.nav[tool["key"]] = item
        self.bind_all("<Control-Return>", lambda e: self.run_primary())
        self.show("home")

    def setup_style(self):
        st = ttk.Style(self)
        st.theme_use("clam")
        st.configure("Accent.TButton", background=C["accent"], foreground="#FFFFFF", borderwidth=0,
                     focusthickness=0, padding=(16, 7), font=(FONT, 10, "bold"))
        st.map("Accent.TButton", background=[("active", C["accent_dark"]), ("pressed", C["accent_dark"])])
        st.configure("Soft.TButton", background="#E2E8F0", foreground=C["text"], borderwidth=0, focusthickness=0,
                     padding=(12, 7), font=(FONT, 9))
        st.map("Soft.TButton", background=[("active", "#CBD5E1")])
        st.configure("Mini.TButton", background=C["card"], foreground=C["accent"], borderwidth=0, focusthickness=0,
                     padding=(8, 2), font=(FONT, 9))
        st.map("Mini.TButton", background=[("active", "#EEF2FF")])
        st.configure("Card.TCheckbutton", background=C["card"], foreground=C["text"], font=(FONT, 9))
        st.map("Card.TCheckbutton", background=[("active", C["card"])])
        st.configure("TEntry", fieldbackground="#FFFFFF", bordercolor=C["border"], padding=4)
        st.configure("TCombobox", fieldbackground="#FFFFFF", bordercolor=C["border"], padding=4)
        st.configure("Treeview", rowheight=px(26), font=(FONT, 9), background=C["card"],
                     fieldbackground=C["card"], borderwidth=0)
        st.configure("Treeview.Heading", font=(FONT, 9, "bold"), background="#EEF2FF", foreground=C["text"],
                     borderwidth=0)
        st.map("Treeview", background=[("selected", "#C7D2FE")], foreground=[("selected", C["text"])])
        self.option_add("*TCombobox*Listbox.font", (FONT, 9))

    def show(self, key):
        if self.current is not None:
            self.current.pack_forget()
        if key not in self.pages:
            self.pages[key] = self.make_home() if key == "home" else PAGES[key](
                self, next(t for t in TOOLS if t["key"] == key))
        self.current = self.pages[key]
        self.current.pack(fill="both", expand=True)
        for k, item in self.nav.items():
            item.set_active(k == key)
        self.set_status("Ready")

    def make_home(self):
        page = tk.Frame(self.content, bg=C["bg"])
        banner = tk.Frame(page, bg=C["accent"])
        banner.pack(fill="x", padx=24, pady=(24, 8))
        tk.Label(banner, text="Welcome to DevToolkit", bg=C["accent"], fg="#FFFFFF",
                 font=(FONT, 22, "bold")).pack(anchor="w", padx=28, pady=(22, 2))
        tk.Label(banner, text="Ten converters and generators for everyday development work.\n"
                              "Pick a tool below or from the sidebar - everything runs locally on your computer.",
                 bg=C["accent"], fg="#E0E7FF", font=(FONT, 11), justify="left").pack(anchor="w", padx=28,
                                                                                     pady=(0, 22))
        grid = tk.Frame(page, bg=C["bg"])
        grid.pack(fill="both", expand=True, padx=16, pady=8)
        for c in range(5):
            grid.columnconfigure(c, weight=1, uniform="card")
        for i, tool in enumerate(TOOLS):
            ToolCard(grid, i + 1, tool, lambda k=tool["key"]: self.show(k)).grid(
                row=i // 5, column=i % 5, padx=8, pady=8, sticky="nsew")
        return page

    def set_status(self, msg, error=False):
        self.status_label.config(text=msg, fg=C["err"] if error else C["muted"])

    def run_primary(self):
        if self.current is not None and hasattr(self.current, "primary"):
            self.current.primary()


def main():
    if IS_WIN:
        try:
            import ctypes
            ctypes.windll.shcore.SetProcessDpiAwareness(1)  # crisp text on high-DPI screens
        except Exception:
            pass
    App().mainloop()


if __name__ == "__main__":
    main()
