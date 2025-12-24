---
description: 'Add OCaml documentation'
tools: ['vscode', 'execute', 'read', 'edit', 'search', 'web', 'agent', 'ms-vscode.vscode-websearchforcopilot/websearch', 'todo']
---

Goal and Scope
--------------
- For every file in the OCaml codebase, and for any construct that lacks documentation, look for normal comments `(* ... *)` around it.
- If they are documenting the construct, convert them to proper OCaml documentation comments `(** ... *)` and minimally enhance formatting.
- If no comments are found, do not add any documentation.
- Only modify comments that act as documentation, and only to change them to proper OCaml documentation comments and formatting. Do not move comments across elements or introduce blank lines that could break association.
- If a documentation comment includes author information, preserve it by adding corresponding `@author` tags.
- Do not alter the wording of comments being converted beyond changing their delimiters; keep original phrasing even if imperfect.

Association and Placement Rules
-------------------------------
- `.mli` files: A special comment associates to the nearest element before or after if there is no blank line or another special comment between them. For constructors and record fields, the associated comment must be placed after the constructor/field, with no blank lines or comments between.
- `.ml` files: A special comment associates to the following element if placed immediately before it without any blank line. For constructors and record fields, the comment must be placed after, before the `|` if another constructor follows.
- Do not change code or move comments; preserve adjacency so association is maintained. Comments beginning with `(*` and more than two `*` (e.g., banners) are ignored by OCamldoc—do not convert those.

Formatting Conversion (OCamldoc Markup)
---------------------------------------
When converting formatted content from other styles (Markdown, ad-hoc text), use the standard OCamldoc syntax:
- Text emphasis: `{b ...}` for bold, `{i ...}` for italic, `{e ...}` for emphasis.
- Headers: `{[0-9] ...}` as section headers; optionally `{[0-9]: label ...}` to set a reference label.
- Lists:
	- Shortcut: keep a single list as lines starting with `-` (unordered) or `+` (ordered), terminated by a blank line.
	- Explicit: `{ul {- item 1} {- item 2}}` or `{ol {li item 1} {li item 2}}`.
- Code and preformatted:
	- Inline code: `[ string ]`.
	- Preformatted source: `{[ string ]}`.
	- Verbatim block: `{v string v}`.
- Links: `{{: url } text}`.
- Cross-references: `{!Fully.Qualified.name}` or disambiguate with a class prefix, e.g., `{!type:Foo.Bar.t}`, `{!val:Foo.Bar.t}`, `{!const:tree.Node}`, `{!recfield:Mod.tree.field}`.
- Target-specific: `{% latex or html or texi or man content %}` (use sparingly; default is LaTeX if target omitted).
- HTML tags: `<b>`, `<i>`, `<code>`, `<ul>`, `<ol>`, `<li>`, `<center>`, `<hN>` are recognized and may be used instead of their OCamldoc equivalents.
- Escaping: Escape special characters `{`, `}`, `[`, `]`, and `@` inside text with `\`.

Tags (@-tags)
-------------
Convert structured parts of comments into appropriate `@`-tags when the intent is clear from existing text. Do not invent content.
- `@param id text`: Document parameters for functions, methods, classes, functors.
- `@return text`: Describe return value.
- `@raise Exc text`: Document possible exceptions.
- `@author string`: One per author; multiple allowed.
- `@since string`, `@version string`, `@before version text`.
- `@see <URL> text`, `@see 'filename' text`, `@see "document-name" text`.

First Sentence
--------------
- Ensure the comment begins with a clear first sentence summary. The first sentence ends at the first `.` followed by a blank, or the first blank line, excluding certain formatted blocks (`{ul}`, `{ol}`, `[ ]`, `{[ ]}`, `{v v}`, `{% %}`, `{! }`, `{^ }`, `{_ }`).

Stop Special Comment
--------------------
- If a normal comment clearly indicates “stop documenting subsequent items” within a class/module scope, convert it to `(**/**)` to stop documentation from that point until the end of the scope or until the next stop comment. Do not add stop comments unless the intent is explicit in existing comments.

Examples
--------
- Markdown list to OCamldoc:
	- Input: `(* Features:\n - fast\n - safe\n *)`
	- Output: `(** Features\n - fast\n - safe\n *)`
- Parameter description:
	- Input: `(* f x y: adds x and y. x: first int; y: second int; returns sum *)`
	- Output: `(** Adds two integers.\n @param x first integer\n @param y second integer\n @return sum of x and y *)`
- Constructor comment (after the constructor):
	- `type weather = | Rain of int (** Amount in mm *) | Sun (** Clear sky *)`

Operational Guidance
--------------------
- Preserve code and non-documentation comments; only convert documentation-like comments.
- Do not move comments; keep them adjacent to the element to retain association.
- Do not insert blank lines between a documentation comment and its element.
- Do not convert banner comments with more than two asterisks.

Checklist
---------
- Adjacent placement preserved (.mli/.ml rules respected).
- Converted to `(** ... *)` with correct markup and escapes.
- Lists, code blocks, links, and cross-references formatted per OCamldoc.
- Tags applied only when clearly supported by existing text.
- Constructors/record fields documented after their definitions.
- Clear first sentence provided without inventing content.

Reference
---------
- Documentation syntax details: [./ocamldoc.txt](./ocamldoc.txt)