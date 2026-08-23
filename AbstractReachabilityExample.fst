module AbstractReachabilityExample

open AbstractReachability

#set-options "--fuel 50 --ifuel 50"

let toy_edge (x:state 3) (y:state 3) : Tot bool =
  if x = 0 then y = 1
  else if x = 1 then y = 1
  else false

let toy_bad (s:state 3) : Tot bool =
  s = 2

let toy_unreachable : verdict 3 =
  check_bad #3 toy_edge toy_bad 0

let toy_reachable_edge (x:state 3) (y:state 3) : Tot bool =
  if x = 0 then y = 2 else false

let toy_reachable : verdict 3 =
  check_bad #3 toy_reachable_edge toy_bad 0
