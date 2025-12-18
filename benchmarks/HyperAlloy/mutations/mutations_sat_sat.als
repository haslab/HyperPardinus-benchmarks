open util/natural

trace sig Machine {
  var water : one Natural,
  var input : lone Input,
  var output : lone Output,
}
enum Output { Coffee, Tea }
enum Input { Req, Fill }

pred machine[m:Machine] {
  no m.output
  no m.input
  m.water = inc[One]
  always {
    m.input = Req and gt[m.water,Zero] implies some m.output'
    not (m.input = Req and gt[m.water,Zero]) implies no m.output'
    m.input = Fill and m.water = Zero implies m.water' = inc[One]
    m.input = Req and gt[m.water,Zero] implies m.water' = dec[m.water]
    not (m.input = Fill and m.water = Zero) and not (m.input = Req and gt[m.water,Zero]) implies m.water' = m.water
  }
}

pred mutant[m:Machine] {
  no m.output
  no m.input
  m.water = inc[One]
  always {
    m.input = Req and gt[m.water,Zero] implies some m.output'
    not (m.input = Req and gt[m.water,Zero]) implies no m.output'
    m.input = Fill and m.water = Zero implies m.water' in One
    m.input = Req and gt[m.water,Zero] implies m.water' = dec[m.water]
    not (m.input = Fill and m.water = Zero) and not (m.input = Req and gt[m.water,Zero]) implies m.water' = m.water
  }
}

pred same_input[m1,m2:Machine] {
  m1.input = m2.input
}

pred same_output[m1,m2:Machine] {
  m1.output = m2.output
}

run PotentiallyKillable { 
  some m1:Machine | mutant[m1] and all m2:Machine |
     (machine[m2] and always same_input[m1,m2]) implies
       eventually not same_output[m1,m2]
} for 10 steps, 3 Natural, 0 Int expect 1

run DefinitelyKillable { 
  some m1:Machine | machine[m1] and all m2,m3:Machine |
     (mutant[m2] and machine[m3] and always (same_input[m1,m2] and same_input[m1,m3])) implies
       eventually not same_output[m2,m3]
} for 10 steps, 3 Natural, 0 Int expect 1

