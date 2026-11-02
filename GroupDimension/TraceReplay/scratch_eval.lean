import GroupDimension.TraceReplay.Data.Rips10
open GroupDimension.TraceReplay
#eval Rips10.trace.levels.map (fun l => (l.1, l.2.length))
#eval match runLevels Rips10.trace Rips10.trace.levels 1 [] with
  | none => "levels out of order"
  | some (k, cur) => s!"k={k} vectors={cur.length} sizes={(cur.take 5).map (·.2.length)}"
#eval check Rips10.trace Rips10.members
