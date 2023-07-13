@present SchTuringMachine(FreeSchema) begin
  H :: Ob
  T :: Ob
  States :: AttrType
  Marks :: AttrType
  p :: Hom(H,T)
  l :: Hom(T,T)
  r :: Hom(T,T)
  state :: Attr(H,States)
  marks :: Attr(T,Marks)
end
@acset_type TuringMachine(SchTuringMachine)

T = @acset TuringMachine{enums.TwoStates,enums.BinaryMarks} begin
  H = 1
  T = 128
  p = [1]
  r = [2:128;1] #would be nice to get lambdas here!
  l = [128;1:127]
  state = [enums.start]
  marks = [enums.O;map(x->enums.Blank,1:5);enums.X;map(x->enums.Blank,1:121)]
end
M = @migration SchTuringMachine SchTuringMachine begin
  H => H
  T => T
  States => States 
  Marks => Marks 
  p => begin 
        υ(m,s) = m == Main.TestDiagrammaticPrograms.enums.Blank ? r :
                  m == Main.TestDiagrammaticPrograms.enums.O ? r : identity
        x->υ(marks(p(x)),state(x))(p(x))
      end
  state => begin 
        σ(m,s) = s == Main.TestDiagrammaticPrograms.enums.stop ? Main.TestDiagrammaticPrograms.enums.stop :
                 m == Main.TestDiagrammaticPrograms.enums.X ? Main.TestDiagrammaticPrograms.enums.stop :
                 Main.TestDiagrammaticPrograms.enums.start
        x -> σ(marks(p(x)),state(x))  
      end
  r => r
  l => l
  marks => begin 
            μ(m,s) = s == Main.TestDiagrammaticPrograms.enums.start ? 
                    (m == Main.TestDiagrammaticPrograms.enums.Blank ? Main.TestDiagrammaticPrograms.enums.O :
                     m == Main.TestDiagrammaticPrograms.enums.O ? Main.TestDiagrammaticPrograms.enums.O : Main.TestDiagrammaticPrograms.enums.X) :
                     m
            x -> x == p(1) ? μ(marks(x),state(1)) : marks(x)
            end
  end
  M = @migration SchTuringMachine SchTuringMachine begin
    H => H
    T => T
    States => States 
    Marks => Marks 
    p => begin 
          υ(m,s) = m == Main.enums.Blank ? r :
                    m == Main.enums.O ? r : identity
          x->υ(marks(p(x)),state(x))(p(x))
        end
    state => begin 
          σ(m,s) = s == Main.enums.stop ? Main.enums.stop :
                   m == Main.enums.X ? Main.enums.stop :
                   Main.enums.start
          x -> σ(marks(p(x)),state(x))  
        end
    r => r
    l => l
    marks => begin 
              μ(m,s) = s == Main.enums.start ? 
                      (m == Main.enums.Blank ? Main.enums.O :
                       m == Main.enums.O ? Main.enums.O : Main.enums.X) :
                       m
              x -> x == p(1) ? μ(marks(x),state(1)) : marks(x)
              end
    end
  run_TM(T,n) = n == 0 ? T : run_TM(migrate(TuringMachine,T,M),n-1)
  @test begin subpart(run_TM(T,10),1:8,:marks) ; true end # Union{AttrVar,BinaryMarks}[map(x->enums.O,1:6);enums.X;enums.Blank]