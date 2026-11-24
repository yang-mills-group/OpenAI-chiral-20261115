import YM.CF.Sedge.Plume
/-! Exact finite-fermion transform including external word. Bool true denotes holes here. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fock
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Finset NormedSpace Filter Function
attribute [local instance] opCStarAlgebra
variable {n m:Type*}[LinearOrder n][Fintype n][LinearOrder m][Fintype m]
variable (f:m↪n)(s:Finset n)(e:Deck f s)
variable {P: Op m} (h:IsStarProjection P) {B:Op n}(b:B=addS f s P){Q W V K Y: Op n}(g:Clad Q B W V K)(hu:Clad (1-Q) (1-B) V W Y)
include b h g hu e
-- outputs operator explicitly via adjoint range inverses (no need diagonalize)
def clair (i:Cod n):= (fun K T:Op n=> creed i.1 (trailK f (acts (star (rone K T i)) (basisKet i.2))))
lemma alaye (x:Wave n)(i:Cod n): pailL f s (acts (detail K Y i) x)=acts (clair f i K Y) (pailL f s x):=by
  rcases i with ⟨d,i⟩; cases d
  · apply planter _ _ e P; rw [←b]; exact stayB g hu i
  apply rattan _ _ e P; rw [←b]; exact stateB g hu i
lemma tuneup (v:Cod n) : clair f v K Y=∑ i:m,(if v.1 then K v.2 (f i) else star (Y v.2 (f i))) • cry P (v.1,i):=by
  rcases v with ⟨c,u⟩; dsimp only; cases c
  · let x:=trailK f (acts (star Y) (basisKet u))
    change create x= _
    have hp: acts P x=0:=by unfold x; rw [←pane _ _ e,← b,stayB g hu,map_zero]
    have hx:x=acts (1-P) x:=by rw [act_sub,hp,act_one,sub_zero]
    have hy(i):x.ofLp i=star (Y u (f i)):=by unfold x; rw [seamK,basis_act]; rfl
    nth_rw 1 [hx]; rw [←basis_expand x,map_sum,map_sum]; refine sum_congr rfl ?_; intro i _; rw [map_smul,map_smul, hy]; change _=star _ • seekF _ _; rw [seekF,prong_p]
  let x:=trailK f (acts (star K) (basisKet u)); change remove x=_
  have hp: x=acts P x:=by unfold x; rw [←pane _ _ e,←b,stateB g hu]
  have ht(i):star (x.ofLp i)=K u (f i):=by unfold x; rw [seamK,basis_act]; exact star_star _
  nth_rw 1 [hp]; rw [←basis_expand x,map_sum]; unfold remove; rw [map_sum,star_sum]; apply sum_congr rfl; intro i _; rw [map_smul,map_smul,star_smul,ht]; change _=K _ _ • hideF _ _; rw [hideF,prong_t]
lemma perch (p:Wave n)(q:Wave m)(hv:Sea P q)(hz:Sea Q p)(l:List (Cod n)):
     pailL f s (acts (quant W) (acts (rollC (cry Q) l) p))= (skyGlow (hoist f s q) W p) •
                  acts (exp (dg (summit f (laneP B W K)))) (((claps l).map (invest (fun i=>clair f i K Y) q (chordP Q B W V K Y))).sum):=by
  let u:=hoist f s q; have hB:Sea B u:=b.symm ▸ stageUp f s e h hv
  let T:= laneP B W K; let U:=1-T; let L:=exp (dg T); let A:=quant U * quant W
  let a:=skyGlow u W p
  have he:L* A= quant W:=by rw [show L=quant (1+T) from tallied T g.reef]; change _*(_*_)=_; rw [← mul_assoc, ←quant_mul,g.flick,quant_one,one_mul]
  have ht : quant U *L=1:=by rw [show L=quant (1+T) from tallied T g.reef]; rw [←quant_mul,mul_eq_one_comm.mp g.flick,quant_one]
  have hΓ: acts A p=a • u:=by unfold A; rw [act_mul,broomstick g p u hz hB,map_smul,←act_mul, ht,act_one]
  let G:=detail K Y; let Y':=cravat Q B W V K; let d:=chordP Q B W V K Y;
  have hy(l'):A*rollC (cry Q) l'=rollC Y' l'* A:=by
    induction l' with
    | nil=>simp [rollC]
    | cons i l ih=> change A*(_*rollC _ l)=Y' i*rollC Y' l*A; rw [←mul_assoc,(show A*cry Q i=Y' i*A from hangs g i), mul_assoc,ih, ←mul_assoc] -- tune
  let R:=pailL f s
  let F:=fun i=> clair f i K Y
  have hP(c): R (invest G u d c)=invest F q d c:=by
    unfold invest; rw [map_smul]; congr 1
    generalize c.term=v; induction v with
    | nil=> rw [emptyChime,emptyChime]; exact pourL _ _ e q
    | cons i l ih=> rw [charm,charm,show R (acts (G i) _)=acts (F i) (R _) from alaye f s e h b g hu _ i,ih]
  change pailL _ _ _=a • _
  rw [show quant W=L*A from he.symm]; rw [act_mul,←act_mul A,hy,act_mul,hΓ,map_smul, map_smul, map_smul]
  have hg: addS f s P*T=0:=b ▸ g.bare; have hY:T*addS f s P=T:=b ▸ g.chest
  rw [show acts (rollC Y' _) _=_ from shadeW Y' G (draw Q B W V K) u d (slump g hu u hB) (contr Q B W V K Y) (cloth g hu) l]; unfold L; rw [tides _ _ e h hg hY];
  congr 2; -- fix
  change R _=_; rw [map_list_sum]; -- tune
  simp_rw [List.map_map, show R ∘ invest G u d=invest F q d from funext hP]; rfl
end YM.CF.Fock
