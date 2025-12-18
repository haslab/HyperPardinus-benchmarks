open util/ordering[Position]
sig Position {}

trace sig Board {
  obstacles : Position -> Position,   -- obstacles as set of position pairs
  goals : Position -> Position,       -- goals as set of position pairs
  var robot : Position -> Position,   -- robot position as set of position pairs
}

pred moveleft[b:Board] {
  some next.(b.robot) and no next.(b.robot) & b.obstacles 	-- guard: move if position exists and not obstacle
  b.robot' = next.(b.robot)								  	-- effect: move robot
}

pred moveright[b:Board] {
  some prev.(b.robot) and no prev.(b.robot) & b.obstacles 	-- guard: move if position exists and not obstacle
  b.robot' = prev.(b.robot)								  	-- effect: move robot
}

pred moveup[b:Board] {
  some (b.robot).next and no (b.robot).next & b.obstacles 	-- guard: move if position exists and not obstacle
  b.robot' = (b.robot).next								  	-- effect: move robot
}

pred movedown[b:Board] {
  some (b.robot).prev and no (b.robot).prev & b.obstacles 	-- guard: move if position exists and not obstacle
  b.robot' = (b.robot).prev								  	-- effect: move robot
}

pred stutter[b:Board] {
  b.robot' = b.robot										-- do nothing
}

let p0[] { first }
let p1[] { first.next }
let p2[] { p1.next }
let p3[] { p2.next }
let p4[] { p3.next }
let p5[] { p4.next }
let p6[] { p5.next }
let p7[] { p6.next }
let p8[] { p7.next }
let p9[] { last }

pred board[b:Board] {
  no b.obstacles & b.goals									-- goals do not overlap with obstacles
  b.goals = last -> last									-- fix a goal at top-right
  b.obstacles =					   							-- fix some obstacles
	p5 -> p0 + p7 -> p0 + p3 -> p1 + p9 -> p1 + p1 -> p3 + 
	p3 -> p3 + p6 -> p3 + p3 -> p4 + p5 -> p4 + p6 -> p4 + 
	p7 -> p4 + p1 -> p5 + p3 -> p5 + p4 -> p5 + p9 -> p5 + 
	p1 -> p6 + p2 -> p6 + p3 -> p6 + p4 -> p6 + p6 -> p6 + 
	p6 -> p7 + p6 -> p8 + p1 -> p8 + p2 -> p8 + p3 -> p8 + 
	p1 -> p9 + p2 -> p9 + p4 -> p9 
  always one b.robot
  b.robot = first -> first 									-- fix starting position at bottom-left
 
  always {													-- allowed events
    moveleft[b] or moveright[b] or moveup[b] or movedown[b] or stutter[b]
  }
  eventually b.robot in b.goals								-- the robot eventually reaches a goal
}

pred Path {
  some b1:Board | board[b1] and all b2:Board | board[b2] implies always (b2.robot in b2.goals implies b1.robot in b1.goals)
} 

run Path for 10 Position, 20 steps, 0 Int expect 1

