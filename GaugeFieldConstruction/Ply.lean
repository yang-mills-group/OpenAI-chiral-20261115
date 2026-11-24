import GaugeFieldConstruction.Plank
/- Gauge average phase extensions. -/
set_option autoImplicit false
set_option maxRecDepth 5500
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
namespace MastTin
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
variable {p:BudgetPoint} (o:Skye.Seat n)
open TableF.Lenten.Loden Haro Tap Hove Moto
attribute [local instance] opCStarAlgebra
variable {h v:ℝ}
open Dial Nacre Ember Fir Fock
-- mark support
abbrev Scuff (X:Hubber n): Finset (Single n):=univ.filter fun i=> node i.1.1∈ X
lemma scuff_G(X Y:Hubber n)(t: Disjoint X Y): Disjoint (Scuff X) (Scuff Y):= disjoint_left.mpr fun i k s=> disjoint_left.mp t (mem_filter.mp k|>.2) (mem_filter.mp s|>.2)
lemma tickets_E(A: Paper n){X:Hubber n}(u:TrackD p X h A v)(W:Pane n): Sector (Scuff X) false (marketD A W):=by
 apply Sector.sumS; intro i _; obtain ⟨z,c,-⟩:=u; by_cases q:DomainP X i
 · apply Sector.scale; rcases i with _|⟨b,i,j⟩; · exact Sector.one
   cases b
   · exact (Sector.down i (mem_filter.mpr ⟨mem_univ _,q.1⟩)).mul (Sector.up j (mem_filter.mpr ⟨mem_univ _,q.2⟩))
   exact (Sector.up i (mem_filter.mpr ⟨mem_univ _,q.1⟩)).mul (Sector.down j (mem_filter.mpr ⟨mem_univ _,q.2⟩))
 rw [(c i).2 q,Pi.zero_apply,zero_smul]; exact Sector.zero _
lemma matrix_R(i:Single n): i∈Tset n ↔ i.1.2∈ plusHalf:=by
 unfold Tset; rw [mem_preimage,show (helix n) i=(i.1.1,i.1.2,i.2) from rfl]; simp [Lat.upperP] -- tune name
abbrev GiftS : Finset Kt:=univ.filter fun x=>x.1∈ plusHalf
lemma Gift_p : baseF false=cutM GiftS:=by
 change Ember.bins SU.Slot=_; unfold Ember.bins; rw [show Aop=cutM plusHalf from (raising.trans Adef.symm).symm]; ext ⟨x,y⟩ ⟨l,h⟩; by_cases v:x=l <;> by_cases q:y=h <;> simp [Fock.cutM, GiftS,v,q] -- norm tun
lemma Gift_m: baseF true=cutM GiftSᶜ:=by change 1-baseF false=cutM GiftSᶜ; rw [Gift_p]; ext i j; by_cases q:i=j <;> by_cases t:i∈GiftS <;> by_cases e:j∈GiftS <;> simp only [Fock.cutM,mem_compl,Matrix.sub_apply,Matrix.one_apply,Matrix.diagonal_apply,q,t,e] <;> aesop
private lemma fatt(i:Single n): portB i∈GiftS ↔ i∈Tset n:=by rw [GiftS,mem_filter,and_iff_right (mem_univ _)]; exact (matrix_R i).symm
lemma leafT (F:hart_X n)(b:Bool) (A: Pane n)(i j:Single n)(v:Mott b (F A))(w:plac F b (some (b,i,j)) A≠0): match b with
| true=>i ∉ Tset n
| false=> i∈Tset n:=by
 cases b
 · let x:= matPH (F A) j.1.1 i.1.1; let Y:= portB i; let X:= portB j
   by_contra h; have ht: Y∉GiftS:= mt (fatt i).mp h
   have hp:x X Y=0:=by rw [← (show x*baseF false=x from (v _ _).r),Gift_p]; unfold Fock.cutM; rw [Matrix.mul_diagonal,if_neg ht,mul_zero]
   exact w (show plac F false _ A=0 from (show -(F A j i)=0 from neg_eq_zero.mpr hp)) -- plac if self reduces false
 intro h; let x:= matPH (F A) i.1.1 j.1.1; let Y:= portB i; let X:=portB j; have ht:Y∉ GiftSᶜ:= mem_compl.not.mpr (not_not_intro ((fatt i).mpr h))
 apply w; change x Y X=0; rw [← (show baseF true*x=x from (v _ _).l),Gift_m]; unfold Fock.cutM; rw [Matrix.diagonal_mul,if_neg ht,zero_mul]
lemma halt_L(F: hart_X n)(b:Bool)(A:Pane n)(v:Mott b (F A))(Y: Phys n): letterRead (marketD (plac F b) A) Y=0:=by
 let M:=mateK n; let T:=Tset n; have he: M=M.ofLp T • basisKet T:= calc
    _ = acts (lineOp (tickA n)) M := (tickB n).1.symm
    _ = _ := by rw [touchP,cutLine,cut_oneAct]
 let X:= marketD (plac F b) A; suffices h: acts (star X) M=0 by
    change inner ℂ M (acts X Y)=0; rw [← act_inner (A:=X),h,inner_zero_left] -- tune statement
 unfold X marketD; rw [star_sum,act_sum]; apply sum_eq_zero; intro k _; by_cases t:plac F b k A≠0
 · rw [star_smul,act_smul]; rcases k with _|⟨u,i,j⟩; · exact (t rfl).elim
   by_cases e:b=u; swap; · exact (t (show plac F b _ A=0 from (by simp [plac,Ne.symm e]))).elim
   subst u; -- star acts
   let P:= dot_Q (some (b,i,j)); have hp:= leafT F b A i j v t; have hx: acts (star P) M=0:=by
      let z:= M.ofLp T; rw [he,map_smul]; cases b
      · change _ • (acts (star (takeF i*put j)) (basisKet _))=0; rw [star_mul,takeF,star_star,act_mul,put_act,if_pos hp,map_zero,smul_zero]
      change _ • (acts (star (put i*takeF j)) (basisKet _))=0; rw [star_mul,act_mul, show star (put i)=takeF i from rfl, take_act,if_neg hp,map_zero,smul_zero]
   rw [hx, smul_zero]
 rw [Classical.not_not.mp t,zero_smul,star_zero,act_zero] -- act_zero type
lemma hush_o (F: hart_X n)(b:Bool)(A:Pane n)(t:Mott b (F A))(X:Hubber n)(j: Disjoint (Pach o) X)(p':TrackD p (Pach o) h (plac F b) v)(S:FC (Single n))(f: Sector (Scuff X) false S)(Y:Phys n):letterRead (S* marketD (plac F b) A) Y=0:=by
 have he:=Sector.apart (tickets_E (plac F b) p' A) f (scuff_G (Pach o) X j); rw [show S*marketD _ _= marketD (plac F b) A*S from (by simpa [Sector.grainB] using he.symm)]
 change inner ℂ (mateK n) (acts _ _) =_; rw [act_mul]; exact halt_L F b A t (acts S Y)
lemma exportE {I:Type*}(T:Finset I)(L:I→Op (Single n))(t:Bool)(u:∀ i∈T,Mott t (L i)): Mott t (∑ i∈ T,L i):=by
 intro x y; rw [show matPH (∑ i∈T,L i) x y=∑ i∈T,matPH (L i) x y from ?_]; constructor; rw [Matrix.mul_sum]; exact sum_congr rfl fun i v=> (u i v x y).l; rw [Matrix.sum_mul]; exact sum_congr rfl fun i v=> (u i v x y).r; ext i j; change (∑ i∈T,L i) _ _=_; simp only [Matrix.sum_apply]; rfl -- tune
lemma bellY {I:Type*}(T:Finset I)(F:I→ FC (Single n))(S:FC (Single n))(W:Phys n): letterRead (S*∑ i∈T,F i) W=∑ i∈T,letterRead (S*F i) W:=by
 rw [mul_sum]; change (innerSL ℂ (mateK n)) (acts _ W)=_; rw [act_sum,map_sum]; rfl -- act_sum binder universe
open Taxi TableF Bank HushP ModuleB
abbrev Tolω:ℝ:=(Fintype.card lotV:ℝ)* abs tentRate* pentCost
abbrev Pyl (b:Bool)(o:Seat n)(F:yardLot)(h:ℝ):Paper n:=∑ i:lotV,plac (beamer o i (fun _=> F i) h) b
lemma shinePH (b:Bool)(P:PalOne)(t:Oneκ b P)(w:0<h)(u:20<n.val)(x:p.power≤3)(q:p.order≤6)(M:Male): let L:=Pyl b o (excels o P) h; let X:= AlphaY L; let U:=orbitPH (X 1); let O:=markJet o U h
 TrackD p (Pach o) h L (Tolω*CostOle P) ∧ portable L∧O.1=P.1 ∧ O.2.1=P.2.1 ∧ (∀ i,Mott b (orbitPH (X i))) ∧ lifeH X=0 ∧ landA M o X p h=0 ∧ ∀ (A:Pane n)(W:Phys n)(S:FC (Single n))(Y:Hubber n), Disjoint (Pach o) Y → Sector (Scuff Y) false S →letterRead (S*marketD L A) W=0:=by
 intro L X U O; let F:=excels o P; let R(s):= SootK b (F s); have hp(s):R s:= excels_H o P t s;
 let B(i):hart_X n:= beamer o i (fun _=>F i) h; let CZ(i):=plac (B i) b; let E:=tentRate*fena F; let d:=Tolω*CostOle P
 have hx(i):TrackD p (Pach o) h (CZ i) E:= marked_w o b _ i (hotB (F i) _ (brew_e F i)) w.ne' u x q
 have hv(i):portable (CZ i):=kinViewP o (fun _=>F i) i (fun A g=> by rw [← ((hp i).η (g o)).eq,mul_assoc,Kin_S,mul_one]) b
 have he: portable L:=port_sum univ CZ fun i _=> hv i
 have ht:TrackD p (Pach o) h L d:=by
    apply track_p (track_sum univ CZ (fun _=> E) (fun i _=>hx i)); rw [sum_const,nsmul_eq_mul,card_univ]; unfold d Tolω E; apply le_trans (b:=(Fintype.card lotV:ℝ)*( |tentRate| *(pentCost*CostOle P))) (mul_le_mul_of_nonneg_left (mul_le_mul (le_abs_self _) (excels_C o P u) (norm_nonneg F) (abs_nonneg _)) (Nat.cast_nonneg _)) (le_of_eq (by ring))
 have hs: X=blurred o F h:=by
    unfold X; rw [show AlphaY L=∑ i:lotV,AlphaY (CZ i) from map_sum AlphaL CZ univ]; apply sum_congr rfl; intro i _; exact funext fun V=> plac_ℓ ..
 have hM(i k):Mott b (B i k):= soot_b o (A:=F i) i (hp i) k
 have hi(i:Pane n): Mott b (orbitPH (X i)):=by
    rw [hs,blurred,Finset.sum_apply,plains]; apply exportE; intro j _; rw [ph_caps]; exact hM j i
 obtain ⟨g,l⟩:=excels_p (h:=h) o P u w.ne'; rw [← (show U=notesK o F h from (congrArg orbitPH (congrFun hs 1)).trans (snap_blur o F))] at g l -- match
 refine ⟨ht,he,g,l,hi,hs.symm ▸ light_blur (h:=h) o F,sill M o X (sprig o ht x q he) hi,fun A W S Y y v'=>?_⟩ -- tune
 rw [show L= _ from (show L=∑ i:lotV,CZ i from rfl),conn_X, Finset.sum_apply,bellY]; exact sum_eq_zero fun i _=> hush_o o _ _ _ (hM i A) Y y (hx i) S v' W
end MastTin
end YM.CF.XGarden
end
