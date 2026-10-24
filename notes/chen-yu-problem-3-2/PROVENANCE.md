# Provenance

## Authorship and AI use

Chuyang Chen is the sole author and coordinator of this independent project. Contact: 22535018@zju.edu.cn. The author identifies GPT-5.5 as the model used for the original manuscript. See [AI_USE.md](AI_USE.md) for the documented roles and acknowledgments.

## Publication edition

The v1.1 publication-format revision reconstructs the supplied June 16, 2026 manuscript in LaTeX. It uses the website's article template: 11pt article, A4, one-inch margins, Latin Modern fonts, a first-page status box, acknowledgments and provenance before the bibliography. Sole author: Chuyang Chen.

The original mathematics was transcribed and checked against the supplied PDF; sections, theorem numbers, equation numbers, and bibliography entries were retained. The original contents list was omitted to match the website template. This is not byte-for-byte preservation of the old PDF. No Lean sources were modified, and the existing conditional verification scope remains unchanged.

This eight-page edition supersedes the earlier eleven-page cover-plus-appendix layout. Editable source: paper.tex.

Original PDF SHA256: E01FF5EBFA5C66DA407485C67D00AA4D59502DE635E0403D79F25C5EAB4C35D6

Typeset PDF SHA256: C7C13EDF5D767438523EFE388125418D58BDF263840033C7233DA146DAC1ACDA

LaTeX source SHA256: C6C735E93C1C56CE75C3ED2CC0EE09BDEB6CF8CEAA541C077945AF27B52C59CB

## Lean source history

The multi-file development was written with AI assistance during the Codex task. It is not an unchanged copy of the original supplied Main.lean, which is not imported by this project. Original Lean SHA256: B76A7C89A589603CE387B45B328C1855F1791ACE5E202F5FAC5010E3EB5A16F4.

The user allowed standard theorems and external papers as inputs while requiring internal arguments to be proved. EXTERNAL_INPUTS.md records the exact implemented boundary, including geometric representation interfaces. The current status remains Conditional F1. No independent human mathematical or statement-correspondence audit is recorded.

The original publication was pushed in commit 88c4a1b; subsequent editorial changes have their own repository history. Earlier validation notes describe their execution-time state.