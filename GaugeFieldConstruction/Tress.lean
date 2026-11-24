import GaugeFieldConstruction.Buttery
/- Echo against actual disjoint spectators. Full combination semantics. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 70000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {K d v t r u c:ℝ}{j k:ℕ}{m B n:Side}
namespace Echo
local notation "GS"=>SU.group
local notation "Λ"=> CSide m B
open Shield F03
open Brace Ledger
variable (o:Seat n)(e:Axis) (f:PlaqAxes)(p:BudgetPoint)
local instance (I:Type)[Fintype I][DecidableEq I]:MeasurableSpace (Op I):=borel _
local instance (I:Type)[Fintype I][DecidableEq I]:BorelSpace (Op I):=⟨rfl⟩
lemma lamp_skip (x:1 < (More n).val)(A A':Pane n)(h:∀ i:Edge (Seat n), i≠(o,e)→ A i=A' i): Lamp o e f p A=Lamp o e f p A':=by
 unfold Lamp TableF.Lenten.HushP.πon; rw [atSite_path, atSite_path]
 obtain ⟨hv,w,t⟩:= spare_L e f; let v:= spare e f; let i: RG.Slot:= TableF.Lenten.HushP.stab (KitP e f)
 let y:=o+step v; have he:y≠o:=by
    letI : Fact (1<(More n).val):=⟨x⟩
    unfold y; intro p; have hp := congrFun p v; have ht : (1:ZMod (More n).val)=0:= add_left_cancel (show (o v : ZMod (More n).val)+1=o v+0 from (by rw [add_zero]; simpa only [Pi.add_apply,step_apply, ↓reduceIte] using hp)); exact one_ne_zero ht
 have hf:slotFace i o=(y,f):=by rw [TableF.Lenten.HushP.rock_v]; simp [KitP,TableF.Lenten.HushP.fanP,TableF.Lenten.HushP.rock,v,y]
 let a:=f.val.1; let b:=f.val.2
 have hy(k:Axis)(hk:v≠k): y+step k≠ o:=by
    letI : Fact (1<(More n).val):=⟨x⟩; unfold y; intro q; have hq:=congrFun q v; simp only [Pi.add_apply,step_apply,if_neg hk, ↓reduceIte,add_zero] at hq; have ht : (1:ZMod (More n).val)=0:= add_left_cancel (show (o v : ZMod (More n).val)+1=o v+0 from hq.trans (add_zero (o v)).symm); exact one_ne_zero ht
 have hu: faceValue A (y,f)=faceValue A' (y,f):=by
    rw [← read_edges,← read_edges]; apply congrArg _; funext j; change A (edges _ _) = A' _; apply h; intro p; have hp:(edges (y,f) j).1=o:=congrArg Prod.fst p; fin_cases j <;> simp only [edges] at hp
    · exact he hp
    · exact hy a w hp
    · exact hy b t hp
    · exact he hp
 have hp: travel A o i.walk=travel A' o i.walk:=by
    change travel A o [posDir v]=travel _ _ [posDir v]; simp [travel,h (o,v) (by simp [hv,v])]
 change p.threshold⁻¹ • SU.group.adjoint (travel A o i.walk) (SU.group.curvature (faceValue A (slotFace i o))) = p.threshold⁻¹ • SU.group.adjoint (travel A' o i.walk) (SU.group.curvature (faceValue A' (slotFace i o))) -- tune congr done earlier
 rw [hp,hf,hu]
abbrev LeadK:= EuclideanSpace.basisFun SU.group.ColorIndex ℝ
abbrev inkMus:= SU.group.ColorIndex
abbrev musk (i:inkMus) : SU.group.Color:= LeadK i
abbrev valMus (q:SU.group.Color)(i:inkMus):= LeadK.repr q i
lemma accent (x:SU.group.Color):∑ i,valMus x i • musk i=x:= LeadK.sum_repr x
lemma at_Ink(g:SU.group.Color): ∑ i:inkMus,valMus g i • at_E o e (musk i)=at_E o e g:=by
 refine Eq.trans ?_ (show Pudge o e (∑ i,valMus g i • musk i)=_ from (by rw [accent,pupq]))
 change _=Pudge o e _; simp_rw [←pupq, map_sum, map_smul]
abbrev dimeT (b:ℝ)(i:inkMus) (U:Pane n):ℝ:=(1/(b*p.threshold))*valMus (Lamp o e f p U) i
lemma contour_val(b:ℝ)(i:inkMus): Continuous (dimeT o e f p b i):=by
 have he: Continuous (Lamp o e f p):=by unfold Lamp TableF.Lenten.HushP.πon Slot.atSite Lattice.expandAt; fun_prop
 apply continuous_const.mul; exact (PiLp.continuous_apply ..).comp (LeadK.repr.continuous.comp he)
variable (q:Clip)(b:ℝ)
abbrev UnEcho (V: marker0 n)(S:marker0 n)(T:trans1 n):= ∫ x:Pane n,letterRead (S x*V x) (T x)∂prior GS (More n)
-- weighted sum accounting
variable {L: Side}{ho:Odd L.val}{Y:Pricing j L ho (Thread j)}(P: Grasp Y B d)
section
variable (o:Seat (CSide m B))(Z:inkMus→ marker0 (CSide m B))
abbrev choiceR (i:inkMus):=Eff o e (musk i) q p b (Z i) (m:=m) (B:=B)
abbrev pasteM (U:Pane Λ):FC (Single Λ):=∑ i:inkMus,dimeT o e f p b i U • choiceR e p q b o Z i U
lemma env_Ln (g:∀ i, Envelope (Z i)):Envelope (pasteM e f p q b o Z):= Env.total _ fun i=> Env.scale (Env.compact (contour_val ..)) (Eff_bound o e _ q p b _ (g i))
private lemma E_cash (u:b≠0)(U:Pane Λ): ∑ i:inkMus, dimeT o e f p b i U • (cashT o e (musk i) q p b U • (1:FC (Single Λ)))=markFee o q e f p b U • (1:FC (Single Λ)):=by
 rw [show markFee o q e f p b U= _ from (show markFee o q e f p b U=Complex.ofReal ((1/(b*p.threshold):ℝ)*ζcone o q p b U (CupT o e f p U)) from ?_), Complex.coe_smul]
 · simp_rw [smul_smul]; rw [←sum_smul]; apply congrArg (· • (1:FC (Single Λ)))
   let g:=Lamp o e f p U; let x:=ζcone o q p b U; nth_rw 1 [show CupT o e f p U= _ from (at_Ink o e g).symm]; change (∑ i,(1/(b*p.threshold)*valMus g i * x (at_E o e (musk i)))) = _* x _; simp_rw [map_sum,map_smul,smul_eq_mul, mul_assoc]; rw [Finset.mul_sum]
 unfold markFee RCore; apply congrArg Complex.ofReal; have ht:=p.threshold_pos; field_simp
lemma grands_L (u:b≠0)(U:Pane Λ): pasteM e f p q b o Z U=markFee o q e f p b U • (1:FC (Single Λ)) - ∑ i:inkMus, dimeT o e f p b i U • (Turret o (G:=GS) p.threshold U • Z i U):=by
 unfold pasteM choiceR Eff; simp_rw [smul_sub]; rw [sum_sub_distrib,E_cash ..]; exact u
open Push.Mark
private lemma hull_pB{I:Type}[Fintype I](F:I→FC (Single n))(A:Phys n): letterRead (∑ i,F i) A=∑ i,letterRead (F i) A:=by
 unfold letterRead; change (innerSL ℂ (Dial.mateK n)) (acts _ A)=_; rw [act_sum,map_sum]; rfl
lemma unitM_u (F:marker0 Λ)(u:untax (m:=m) (B:=B) o e F)(w:∀ i,Envelope (Z i))(T':Envelope (hard q p b P (m:=m)))(c:1<(More Λ).val)(s:∀ i,∀ U∈tight p Λ, HasDerivAt (fun t:ℝ=>changeM P (turnLink (o,e) (musk i) t U) firstM) (acts (Z i U) (changeM P U firstM)) 0): UnEcho (pasteM e f p q b o Z) F (hard q p b P)=0:=by
 let H:=hard (m:=m) q p b P; let S(i:inkMus)(u:Pane Λ): FC (Single Λ):=dimeT o e f p b i u • F u; let V:= choiceR e p q b o Z
 have hp(i:inkMus): untax (m:=m) (B:=B) o e (S i):=by
    refine ⟨Env.scale (Env.compact (contour_val ..)) u.1,fun A A' p=> ?_⟩; -- p shadow
    unfold S dimeT; rw [lamp_skip o e f _ c A A' p,u.2 A A' p]
 let X(i:inkMus)(u:Pane Λ):ℂ:=letterRead (S i u * V i u) (H u); have hv(u:Pane Λ):letterRead (F u * pasteM e f p q b o Z u) (H u)=∑ i:inkMus,X i u:=by
    have he: F u * pasteM e f p q b o Z u=∑ i:inkMus,S i u*V i u:=by
       change F u*_=_; unfold pasteM; rw [mul_sum]; apply sum_congr rfl; intro i _; rw [mul_smul_comm]; exact Eq.symm (smul_mul_assoc (dimeT o e f p b i u) (F u) (V i u))
    rw [he]; exact hull_pB (n:=Λ) (fun i=> S i u * V i u) (H u)
 unfold UnEcho; change (∫ x:Pane Λ,letterRead (F x* pasteM _ _ _ _ _ _ _ x) (H x) ∂ prior GS (More Λ))=_; simp_rw [hv]; rw [integral_finsetSum]; apply sum_eq_zero; intro i _; exact cost_hand o e (musk i) q p b P (Z i) (S i) (hp i) (w i) T' (s i); intro i _; exact Env.integrableX (env_letterRead (env_mult (hp i).1 (Eff_bound o e (musk i) q p b (Z i) (w i))) T') _
end
end Echo
end YM.CF.XGarden
end
