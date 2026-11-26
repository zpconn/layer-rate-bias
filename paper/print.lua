-- The Markdown has one source of truth for the web and print editions.
-- Preserve its inline mathematics and hyperlinks when typesetting native floats.
local function latex(blocks)
  return (pandoc.write(pandoc.Pandoc(blocks), "latex-smart", {wrap_text = "none"}):gsub("%s+$", ""))
end

local function raw(text)
  return pandoc.RawBlock("latex", text)
end

local function heading_label(block)
  if block and block.t == "Para" and block.content[1] and block.content[1].t == "Strong" then
    return pandoc.utils.stringify(block.content[1])
  end
end

local function remove_label(paragraph)
  paragraph.content:remove(1)
  if paragraph.content[1] and paragraph.content[1].t == "Space" then
    paragraph.content:remove(1)
  end
end

local function closes_proof(block)
  return block.t == "Para" and #block.content == 1 and block.content[1].t == "Math"
    and block.content[1].text == "\\square"
end

local function mark_structure(blocks)
  local out = pandoc.Blocks{}
  local i = 1
  local appendix, proof = false, false
  while i <= #blocks do
    local block = blocks[i]
    local next_block = blocks[i + 1]
    local label = heading_label(block)
    if label == "Proof." then
      assert(not proof, "A new proof begins before the previous proof's QED")
      proof = true
      out:insert(raw("\\begin{proof}"))
      remove_label(block)
      if #block.content > 0 then out:insert(block) end
    elseif closes_proof(block) then
      assert(proof, "A QED marker has no preceding proof")
      proof = false
      local last = out[#out]
      if last and last.t == "Para" then
        if #last.content == 1 and last.content[1].t == "Math" and last.content[1].mathtype == "DisplayMath" then
          last.content[1].text = last.content[1].text .. "\\qedhere"
        end
        last.content:insert(pandoc.RawInline("latex", "\\end{proof}"))
      else
        out:insert(raw("\\end{proof}"))
      end
    elseif label == "Lean proof." then
      remove_label(block)
      block.content:insert(1, pandoc.RawInline("latex", "{\\small\\raggedright\\noindent\\textsc{Lean proof.}\\enspace "))
      block.content:insert(pandoc.RawInline("latex", "\\par}"))
      out:insert(block)
    elseif label == "Proof idea." then
      block.content[1] = pandoc.Emph(block.content[1].content)
      out:insert(block)
    elseif label and label:match("^Table %d+%.$") and next_block and next_block.t == "Table" then
      remove_label(block)
      next_block.caption.long = {block}
      out:insert(next_block)
      i = i + 1
    elseif block.t == "Header" and block.level == 1 and block.content[1] and
           block.content[1].t == "Str" and block.content[1].text == "Appendix." then
      if not appendix then out:insert(raw("\\appendix")) end
      appendix = true
      remove_label(block)
      out:insert(block)
    elseif block.t == "Header" and pandoc.utils.stringify(block.content) == "References" and
           next_block and next_block.t == "OrderedList" then
      local entries = next_block.content
      out:insert(raw("\\begin{thebibliography}{" .. #entries .. "}\\label{references}"))
      for number, entry in ipairs(entries) do
        out:insert(raw("\\bibitem{ref-" .. number .. "} " .. latex(entry)))
      end
      out:insert(raw("\\end{thebibliography}"))
      i = i + 1
    else
      out:insert(block)
    end
    i = i + 1
  end
  assert(not proof, "A proof has no closing QED marker")
  return out
end

local function theorem(quote)
  local first = quote.content[1]
  local label = heading_label(first)
  if not label then return end
  local kind = label:match("^([A-Za-z]+) ")
  if kind ~= "Definition" and kind ~= "Lemma" and kind ~= "Proposition"
      and kind ~= "Theorem" and kind ~= "Corollary" then return end
  local title = first.content[1].content:clone()
  local n = title[3] and title[3].text or ""
  assert(n:match("^%d+$") or n:match("^[%dA-Z]+%.%d+$"), "Invalid numbered statement: " .. label)
  for _ = 1, 4 do title:remove(1) end
  assert(#title > 0 and title[1].t == "Str" and title[1].text:match("^%(")
    and title[#title].t == "Str" and title[#title].text:match("%)%.$"),
    "Expected a parenthesized statement title: " .. label)
  title[1].text = title[1].text:sub(2)
  title[#title].text = title[#title].text:sub(1, -3)
  local name = latex({pandoc.Plain(title)})
  local env = "paper" .. kind:lower()
  local counter = kind == "Theorem" and "papertheorem" or "paperlemma"
  remove_label(first)
  local blocks = quote.content
  local opening = "\\begin{" .. env .. "}[{" .. name .. "}]\\checkstatement{\\the" .. counter .. "}{" .. n .. "}"
  if kind == "Theorem" and (n == "1" or n == "2") then
    opening = opening .. "\\pdfbookmark[2]{Theorem " .. n .. " (" .. name .. ")}{main-theorem-" .. n .. "}"
  end
  blocks:insert(1, raw(opening))
  blocks:insert(raw("\\end{" .. env .. "}"))
  return blocks
end

local function bibliography_citation(link)
  if link.target == "#references" then
    local n = pandoc.utils.stringify(link.content):match("^%[(%d+)%]$")
    if n then return pandoc.RawInline("latex", "\\cite{ref-" .. n .. "}") end
  end
end

local function source_link(inline)
  return inline.t == "Link" and (inline.target:find("/formal/", 1, true)
    or inline.target:find("/docs/", 1, true) or inline.target:find("/layer-rates/", 1, true))
end

-- Set the trailing groups of clickable Lean references at citation size, keeping
-- their labels and each destination. A display's source line begins flush left.
local function citations(paragraph)
  local inlines = paragraph.content
  local i = #inlines
  if i == 0 or not source_link(inlines[i]) then return end
  while i >= 5 and inlines[i-1].t == "Space" and inlines[i-2].t == "Str" and
        inlines[i-2].text == "·" and inlines[i-3].t == "Space" and source_link(inlines[i-4]) do
    i = i - 4
  end
  local opening = i == 1 and "\\noindent\\proofsources{" or "\\proofsources{"
  inlines:insert(i, pandoc.RawInline("latex", opening))
  inlines:insert(pandoc.RawInline("latex", "}"))
  return paragraph
end

local function figure(fig)
  local img = fig.content[1].content[1]
  return raw(table.concat({
    "\\begin{figure}[htbp]\\centering",
    "\\includegraphics[width=\\linewidth]{\\detokenize{" .. img.src .. "}}",
    "\\caption{" .. latex(fig.caption.long) .. "}",
    "\\end{figure}",
  }, "\n"))
end

-- Preserve every Lean source character. Spaces and identifier punctuation are
-- legal line breaks in print; indentation is emitted at fixed character width.
local function source_line(line)
  local chars, leading = {}, true
  for _, cp in utf8.codes(line) do
    local ch = utf8.char(cp)
    if ch == " " then
      chars[#chars + 1] = leading and "\\kern\\fontdimen2\\leansource{}" or "\\leangap{}"
    else
      leading = false
      if ch:match("^[A-Za-z0-9]$") then
        chars[#chars + 1] = ch
      else
        chars[#chars + 1] = string.format("\\leanchar{%X}", cp)
        if ch == "." or ch == "_" then chars[#chars + 1] = "\\allowbreak{}" end
      end
    end
  end
  return table.concat(chars)
end

local function code_block(block)
  if not block.classes:includes("lean") then return end
  local lines = {"\\begin{leanscript}"}
  for line in (block.text .. "\n"):gmatch("(.-)\n") do
    lines[#lines + 1] = "\\leanline{" .. source_line(line) .. "}"
  end
  lines[#lines + 1] = "\\end{leanscript}"
  return raw(table.concat(lines, "\n"))
end

local function code_span(code)
  if code.text:find("[\128-\255]") then
    return pandoc.RawInline("latex", "{\\leansource " .. source_line(code.text) .. "}")
  end
  if code.text:match("[/._:%-]") and not code.text:find("[{}\\]") then
    return pandoc.RawInline("latex", "{\\small\\ttfamily\\nolinkurl{" .. code.text .. "}}")
  end
end

local function table_float(tbl)
  -- Left-align the sample description and align the quantitative columns on the right.
  local specs = {"l"}
  for col = 2, #tbl.colspecs do specs[col] = "r" end
  local lines = {"\\begin{table}[htbp]\\centering\\small"}
  if #tbl.caption.long > 0 then lines[#lines + 1] = "\\caption{" .. latex(tbl.caption.long) .. "}" end
  lines[#lines + 1] = "\\begin{tabular*}{\\linewidth}{@{\\extracolsep{\\fill}}" .. table.concat(specs) .. "@{}}\\toprule"
  local function add_rows(rows, header)
    for _, row in ipairs(rows) do
      local cells = {}
      for _, cell in ipairs(row.cells) do
        cells[#cells + 1] = (header and "\\bfseries " or "") .. latex(cell.contents)
      end
      lines[#lines + 1] = table.concat(cells, " & ") .. "\\tabularnewline"
    end
  end
  add_rows(tbl.head.rows, true)
  lines[#lines + 1] = "\\midrule"
  for _, body in ipairs(tbl.bodies) do
    add_rows(body.head, true)
    add_rows(body.body, false)
  end
  add_rows(tbl.foot.rows, false)
  lines[#lines + 1] = "\\bottomrule\\end{tabular*}\\end{table}"
  return raw(table.concat(lines, "\n"))
end

return {
  {Blocks = mark_structure},
  {BlockQuote = theorem, Para = citations, Figure = figure, Code = code_span,
   CodeBlock = code_block, Table = table_float, Link = bibliography_citation},
}
