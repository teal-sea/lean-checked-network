import lean.Pilot
open Lexnet
set_option maxRecDepth 100000
set_option maxHeartbeats 0
example : exactClasses [] = [] := by decide +kernel
example : exactClasses [⟨105, by decide⟩, ⟨110, by decide⟩, ⟨116, by decide⟩, ⟨32, by decide⟩, ⟨102, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨59, by decide⟩] = [2, 2, 2, 0, 3, 10, 10, 10] := by decide +kernel
example : exactClasses [⟨47, by decide⟩, ⟨42, by decide⟩, ⟨120, by decide⟩, ⟨42, by decide⟩, ⟨47, by decide⟩] = [8, 8, 8, 8, 8] := by decide +kernel
example : exactClasses [⟨34, by decide⟩, ⟨47, by decide⟩, ⟨47, by decide⟩, ⟨34, by decide⟩] = [6, 6, 6, 6] := by decide +kernel
example : exactClasses [⟨95, by decide⟩, ⟨83, by decide⟩, ⟨116, by decide⟩, ⟨97, by decide⟩, ⟨116, by decide⟩, ⟨105, by decide⟩, ⟨99, by decide⟩, ⟨95, by decide⟩, ⟨97, by decide⟩, ⟨115, by decide⟩, ⟨115, by decide⟩, ⟨101, by decide⟩, ⟨114, by decide⟩, ⟨116, by decide⟩, ⟨88, by decide⟩] = [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by decide +kernel
example : exactClasses [⟨128, by decide⟩, ⟨255, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩] = [10, 10, 10, 0] := by decide +kernel
