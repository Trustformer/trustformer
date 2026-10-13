(*! [Bounds.report] and [Bounds.witnesses] as OCaml in build/report/, which
    scripts/modes-report.sh compiles and runs. !*)

Require Trustformer.Examples.Criticalities.Bounds.
Require Import ExtrOcamlBasic ExtrOcamlNativeString.

Set Extraction Output Directory "build/report".
Extraction "modes_report.ml" Bounds.report Bounds.witnesses.
