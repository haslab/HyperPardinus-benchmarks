open util/ordering[Position]
sig Position {}

abstract sig Op {}
one sig L, R, U, D extends Op {}

trace sig Board {
  obstacles : Position -> Position,   -- obstacles as set of position pairs
  goals : Position -> Position,       -- goals as set of position pairs
  var robot : Position -> Position,   -- robot position as set of position pairs
  var op : lone Op
}

pred moveleft[b:Board] {
  b.op = L
  some next.(b.robot) and no next.(b.robot) & b.obstacles 	-- guard: move if position exists and not obstacle
  b.robot' = next.(b.robot)								  	-- effect: move robot
}

pred moveright[b:Board] {
  b.op = R
  some prev.(b.robot) and no prev.(b.robot) & b.obstacles 	-- guard: move if position exists and not obstacle
  b.robot' = prev.(b.robot)								  	-- effect: move robot
}

pred moveup[b:Board] {
  b.op = U
  some (b.robot).next and no (b.robot).next & b.obstacles 	-- guard: move if position exists and not obstacle
  b.robot' = (b.robot).next								  	-- effect: move robot
}

pred movedown[b:Board] {
  b.op = D
  some (b.robot).prev and no (b.robot).prev & b.obstacles 	-- guard: move if position exists and not obstacle
  b.robot' = (b.robot).prev								  	-- effect: move robot
}

pred stutter[b:Board] {
  no b.op
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
  b.goals = p6 -> p9 + p7 -> p9 + p8 -> p9  				-- fix some goals
		
  b.obstacles =					   							-- fix some obstacles
	    p5 -> p0 + p6 -> p0 + p7 -> p0 + 
        p8 -> p0 + p9 -> p0 + p6 -> p1 + 
        p7 -> p1 + p8 -> p1 + p9 -> p1 +
        p7 -> p2 + p8 -> p2 + p9 -> p2 + 
        p8 -> p3 + p9 -> p3 + p9 -> p4 + 
        p0 -> p5 + p0 -> p6 + p1 -> p6 + 
        p0 -> p7 + p1 -> p7 + p2 -> p7 + 
        p0 -> p8 + p1 -> p8 + p2 -> p8 + 
        p3 -> p8 + p0 -> p9 + p1 -> p9 + 
        p2 -> p9 + p3 -> p9 + p4 -> p9 
  always one b.robot
  b.robot in p0 -> p0 + p1 -> p0 + p2 -> p0 				-- fix some positions
	     
  always {													-- allowed events
    (moveleft[b] or moveright[b] or moveup[b] or movedown[b] or stutter[b])
  }
}

pred same_behaviour[b1,b2:Board] {
  b1.op = b2.op
}

pred Path {
  some b1:Board | board[b1] and eventually b1.robot in b1.goals and all b2:Board | board[b2] and always same_behaviour[b1,b2] implies eventually b2.robot in b2.goals
} 
run Path for 10 Position, 20 steps, 0 Int expect 1

pred TwoPaths {
  some b1:Board | (board[b1] and eventually b1.robot in b1.goals) and some b2:Board | (board[b2] and eventually b2.robot in b2.goals) and not (always same_behaviour[b1,b2])
} 

run TwoPaths for 10 Position, 20 steps, 0 Int expect 1

