open util/ordering[Position]
sig Position {}
abstract sig Enemy {}
one sig TL, TR, BR extends Enemy {}

trace sig EnemyBoard {
  var robot : Enemy -> one (Position -> Position),
}

trace sig PlayerBoard {
  goals : Position -> Position,
  var robot : Position -> Position,
}

pred moveleft[b:PlayerBoard] {
  some next.((b.robot))
  (b.robot') = next.((b.robot))
}

pred moveright[b:PlayerBoard] {
  some prev.((b.robot))
  (b.robot') = prev.((b.robot))
}

pred moveup[b:PlayerBoard] {
  some (b.robot).next
  (b.robot') = (b.robot).next
}

pred movedown[b:PlayerBoard] {
  some (b.robot).prev
  (b.robot') = (b.robot).prev
}

pred stutter[b:PlayerBoard] {
  (b.robot') = (b.robot)
}

pred clockwise[r:Enemy,b:EnemyBoard] {
  r.(b.robot) in first -> (Position-last) implies r.(b.robot') = (r.(b.robot)).next
  r.(b.robot) in last -> (Position-first) implies r.(b.robot') = (r.(b.robot)).prev
  r.(b.robot) in (Position-first) -> first implies r.(b.robot') = next.(r.(b.robot))
  r.(b.robot) in (Position-last) -> last implies r.(b.robot') = prev.(r.(b.robot))
}

pred board_pc[b:PlayerBoard] {
  always one b.robot
  b.goals = last -> last
  b.robot = first -> first
  always {
    (moveleft[b] or moveright[b] or moveup[b] or movedown[b])
  }
  eventually b.robot in b.goals
}

pred board_en[b:EnemyBoard] {
  b.robot = TL -> first -> last + TR -> last -> last + BR -> last -> first
  always {
    all r:Enemy | (clockwise[r,b])
  }
}

pred Path {
  some b1:PlayerBoard | board_pc[b1] and all b2:EnemyBoard | board_en[b2] implies always (not b1.robot in Enemy.(b2.robot))
}

//run Path for 6 Position, 20 steps, 0 Int expect 1
//run Path for 8 Position, 20 steps, 0 Int expect 1
run Path for 10 Position, 20 steps, 0 Int expect 1

