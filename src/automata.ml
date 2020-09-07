module IntSet = Set.Make(Int)
module CharSet = Set.Make(Char)
module TransitionSet = Set.Make(struct
    type t = (int * char * int)
    let compare = compare
  end)

type t = {
  alpha       : CharSet.t;
  states      : IntSet.t;
  initials    : IntSet.t;
  finals      : IntSet.t;
  transitions : TransitionSet.t
}

let add_state a i = {a with states = IntSet.add i a.states}

let add_transition a t = {a with transitions = TransitionSet.add t a.transitions}

type result = Ok | Ko

let run a s =

  let open TransitionSet in

  let next st c (p, s, _) = s = c && p = st in

  let is_init i = IntSet.mem i a.initials in

  let firsts c = filter (fun (p, s, _) -> s = c && is_init p) a.transitions in

  let rec branch cs (p, _, q) acc =
    if acc = Ok then Ok
    else (loop q cs)

  and loop st s =
    match s with
    | []    -> let open IntSet in
      if mem st a.finals then Ok else Ko
    | c::cs -> let open TransitionSet in
      match filter (next st c) a.transitions with
      | nexts when cardinal nexts = 0 -> Ko
      | nexts -> fold (branch cs) nexts Ko

  in

  fold (branch (List.tl s)) (firsts (List.hd s)) Ko




