import GaugeFieldConstruction.Zephyrus
import YM.CF.Moto.Road
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 30000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
attribute [local instance] opCStarAlgebra
open AnalyticBridge VerifiedReset Taxi
local notation "GS"=> SU.group
variable {n:Side}{p: BudgetPoint}{Q: InkD n}{o:Skye.Seat n}{X:Scree.Hub n}{h c:ℝ}
namespace Lenten
open Bank Laurent Bloch Tap Hove Spire
open Haro Hove Moto Tap
namespace Layout
open HushP ModuleB Pastry
-- entries in PH houses: both endpoints. not represented yet as Mark physical.
abbrev pulseH (X:Op (Single n)):Cipher n:=⟨faceD true false X,face_flour ..⟩
abbrev Whig(i j:Single n):= parity ((true,i):LeanV (Single n)) {(false,j)}
abbrev Wid (i j:Single n):= wire true i*wire false j
lemma whig_1(i j:Single n):‖Whig i j‖=1:=by simp [Whig,parity]
lemma poke_P (i j:Single n):poke (Haro.tray i j)=Whig i j • Wid i j:=by unfold poke Haro.tray; rw [Pastry.Poly.tag_any,Pastry.Poly.tag_once]; rfl; simp -- tune
lemma poke_B(i j:Single n): Wid i j=Whig i j • poke (Haro.tray i j):=by rw [poke_P,smul_smul,Whig,parity_sq,one_smul]
lemma poke_f (F:Op (Single n))(i j:Single n): crumb (pulseH F).val (Haro.tray i j)= F i j*Whig i j:=by
 let T:=Haro.tray i j
 have ht(k l:Single n)(p:(k,l)≠ (i,j)): crumb (Wid k l) T=0:=by rw [poke_B,crumb_scale, chip,if_neg (fun h=>p (Haro.tray_in h.symm)),mul_zero]
 change crumb (faceD true false F) _= _; unfold faceD twinD; simp_rw [crumb_sum,crumb_scale]; rw [sum_eq_single i, sum_eq_single j]
 · rw [show (wire true i * wire false j)= _ from poke_B i j,crumb_scale,chip,if_pos rfl,mul_one]
 · intro y _ p; rw [show crumb _ _=_ from ht i y (by simp [p]),mul_zero]
 · simp
 · intro y _ p; apply sum_eq_zero; intro z _; rw [show crumb _ _=_ from ht y z (by simp [p]),mul_zero]
 simp
lemma poke_none (F:Op (Single n))(T:Finset (Dwell n))(h:∀ i j:Single n,T≠Haro.tray i j): crumb (pulseH F).val T=0:=by
 have he(i j:Single n): crumb (Wid i j) T=0:=by rw [poke_B,crumb_scale,chip,if_neg (h _ _),mul_zero]
 change crumb (faceD true false F) _= _; unfold faceD twinD; simp_rw [crumb_sum,crumb_scale]
 exact sum_eq_zero fun i _=>sum_eq_zero fun j _=>by rw [show crumb _ _= _ from he i j,mul_zero]
lemma spinW (X:Op (Single n)): Haro.orbitPH (pulseH X)=X:=by
 ext i j; rw [Haro.orbitPH,Matrix.of_apply,Prism.port_eq,if_neg (by simp : ((true,i):LeanV _) ≠(false,j))]; rw [show crumb _ _= _ from poke_f X i j,mul_left_comm,parity_sq,mul_one] -- tune
lemma pulse_sc (X:Op (Single n)): Pastry.pane (pulseH X)=0:= mast_free ..
lemma pulse_φ (U:UNI (Single n))(X:Op (Single n)) : pulseH (twist U X) = paintR false false U (pulseH X):=by
 apply Subtype.ext; change faceD true false (twist U X)= twist (quantU (n:=LeanV (Single n)) (closeV U)) (faceD true false X); rw [face_fold,twist_formula]; rfl -- star
lemma pulse_add (X Y:Op (Single n)):pulseH (X+Y)=pulseH X+pulseH Y:=by apply Subtype.ext; unfold pulseH faceD twinD; dsimp only; change _=_+_; simp only [Matrix.add_apply,add_smul,sum_add_distrib]
lemma pulse_src(X:Op (Single n))(w:ℂ): (pulseH (w • X)).val= w • (pulseH X).val:=by unfold pulseH faceD twinD; simp only [Matrix.smul_apply,smul_eq_mul, mul_smul]; erw [Finset.smul_sum]; apply sum_congr rfl; intro i _; rw [Finset.smul_sum]
lemma hall(i:Site n)(k:Hove.Kt): (Moto.hailV i k).1.1=i∧ Hove.portB (Moto.hailV i k)=k:=⟨rfl,rfl⟩
lemma sulk (g:Single n→ℂ): ∑ i:Single n,g i=∑ j:Site n,∑ h:Hove.Kt,g (Moto.hailV j h):=by rw [Fintype.sum_prod_type]; simp_rw [Fintype.sum_prod_type]; rfl
lemma kinG_E (g:Skye.Seat n → SU.E)(i j:Site n): matPH (tradew n g).val i j = if i=j then KinX (g (node i)) else 0:=by
 ext ⟨a,b⟩ ⟨v,y⟩; split_ifs with h
 · subst j; change (tradew n g).val ((i,a),b) ((i,v),y)= KinX (g (node i)) (a,b) (v,y); unfold KinX tradew; simp only [jump_apply,Matrix.kronecker_apply]; by_cases q:a=v
   · subst v; simp
   simp [q] -- tune
 change (tradew n g).val ((i,a),b) ((j,v),y)=0; unfold tradew; simp [jump_apply,h]
lemma matStar (F:Op (Single n))(i j:Site n): matPH (star F) i j = star (matPH F j i):= rfl
lemma matDot (X Y: Op (Single n))(i j:Site n) : matPH (X*Y) i j=∑ k:Site n, matPH X i k *matPH Y k j:=by
 ext a b; change (X*Y) (Moto.hailV i a) (Moto.hailV j b)=_; rw [Matrix.mul_apply,Matrix.sum_apply]; simp_rw [Matrix.mul_apply]; apply Eq.trans (sulk _) _; rfl
lemma matInj (X Y:Op (Single n))(p:∀ i j:Site n,matPH X i j=matPH Y i j):X=Y:=by ext i j; exact Matrix.ext_iff.mpr (p i.1.1 j.1.1) (Hove.portB i) (Hove.portB j)
lemma cabin_x (g:Skye.Seat n→SU.E)(X:Op (Single n))(i j:Site n) : matPH (twist (tradew n g) X) i j= KinX (g (node i))*matPH X i j*star (KinX (g (node j))):=by
 let T:=tradew n g; rw [twist_formula,matDot]; simp_rw [matStar (tradew n g).val,kinG_E]; simp only [apply_ite,star_zero,mul_zero]; rw [sum_ite_eq, if_pos (mem_univ _)]; rw [matDot]; simp only [kinG_E,ite_mul, zero_mul]; simp -- tune
lemma shiftP (x y:Site n)(A B:Pal)(g:Skye.Seat n→ SU.E)(p:B=KinX (g (node x))*A*star (KinX (g (node y)))): twist (tradew n g) (seed_k x y A)=seed_k x y B:=by
 apply matInj; intro i j; rw [cabin_x,star_P,star_P]; split_ifs with h; · rw [←h.1,←h.2,p]
 rw [mul_zero, zero_mul]
lemma hearthP_t (x y:Site n)(A:Pal)(h:node x∈ Pax o)(v:node y∈Pax o): Flour (camp (Pax o)) (pulseH (seed_k x y A)).val:=by
 apply Flour.sum _; intro i _; apply Flour.sum _; intro j _; unfold seed_k; simp only [Matrix.of_apply]; split
 next w=> refine (Flour.putPut _ (mem_filter.mpr ⟨mem_univ ((true,i):Dwell n),?_⟩) (mem_filter.mpr ⟨mem_univ ((false,j):Dwell n),?_⟩)).smul _
          · change node (i.1.1)∈Pax o; rw [←w.1]; exact h
          change node (j.1.1)∈Pax o; rw [←w.2]; exact v
 rw [zero_smul]; exact Flour.trivial -- tune
lemma bright_H (x y:Site n): Continuous fun i:Pal=> pulseH (seed_k x y i):=by
 apply Continuous.subtype_mk; -- bodies via sum
 apply continuous_finsetSum; intro i _; apply continuous_finsetSum; intro j _; unfold seed_k; simp only [Matrix.of_apply]; split_ifs
 · exact (continuous_id.matrix_elem _ _).smul continuous_const
 exact continuous_const
-- costs. Bed for one PH plate
open Housing
private def prosJ (i j:Hove.Kt):Pal→L[ℝ]ℂ:=LinearMap.toContinuousLinearMap ⟨⟨(fun f=> f i j),fun _ _=>rfl⟩,fun _ _=>rfl⟩
abbrev vendors := Hove.Kt ×Hove.Kt
def crustP (V: vendors):= tautF (prosJ V.1 V.2)
lemma Cargo (x y:Site n) (A:Pane n→Pal) (b:ℝ)(p:BudgetPoint)(o:Skye.Seat n)(u: Housing.Haw p o (Pax o) A b)(z:ℂ)(i j:Hove.Kt) : Housing.Haw p o (Pax o) (fun X=>z* A X i j) ((‖z‖*crustP (i,j))* b):=by
 let F: Pal →L[ℝ] ℂ:=z • prosJ i j; let P:=prosJ i j; have he:tautF F=‖z‖*crustP (i,j):=norm_smul ..; apply gum (svelte u F); exact mul_le_mul_of_nonneg_right he.le ((u.rends 1 (ping_f p _)).grade)
lemma ζcard (x y:Site n)(V U:vendors)(t:Haro.tray (Moto.hailV x V.1) (Moto.hailV y V.2)= Haro.tray (Moto.hailV x U.1) (Moto.hailV y U.2)) : V=U:= congrArg (fun i: Single n ×Single n=> (Hove.portB i.1,Hove.portB i.2)) (tray_in (a₁:=(Moto.hailV x V.1,Moto.hailV y V.2)) (a₂:=(Moto.hailV x U.1,Moto.hailV y U.2)) t)
lemma zone_loc (x y:Site n)(A:Pal)(q:Finset (Dwell n))(v:∀ i:vendors,q≠ Haro.tray (Moto.hailV x i.1) (Moto.hailV y i.2)): crumb (pulseH (seed_k x y A)).val q=0:=by
 by_cases h:∃ i j,q= Haro.tray i j; swap; · exact poke_none _ _ (not_exists.mp h|> fun g i=>not_exists.mp (g i))
 obtain ⟨i,j,e⟩:=h; rw [e,poke_f,seed_k,Matrix.of_apply,if_neg,zero_mul]; intro w; obtain ⟨rfl,rfl⟩:=w; exact v (portB i,portB j) e -- tune
abbrev CargoMax:= (25:ℝ)^3* ∑ i: vendors,crustP i
set_option maxHeartbeats 90000 in
set_option maxRecDepth 4000 in
lemma CargoB (x y:Site n)(A:Pane n→Pal)(b:ℝ)(v:Housing.Haw p o (Pax o) A b)(u:p.power ≤3)(h:node x∈Pax o)(t:node y∈ Pax o)
  (q: ℝ)(e:∀ V:Pane n,∀ g:Skye.Seat n→ SU.E,A (Lattice.gauge g V)=KinX (g (node x))* A V* star (KinX (g (node y)))) : PressB p (Zhub o) (fun V=> pulseH (seed_k x y (A V))) q (CargoMax*q^2*b):=by
 let F(i:vendors):= Haro.tray (Moto.hailV x i.1) (Moto.hailV y i.2); have hf:Injective F:= fun i j t=>ζcard x y i j t; let D:=(univ:Finset vendors).image F; let P(T:Finset (Dwell n)):=∑ i:vendors, (Pi.single (F i) (crustP i*b): Finset (Dwell n)→ℝ) T
 have hp(i):0 ≤ crustP i*b:= mul_nonneg (taut_nonneg _) (v.rends 1 (ping_f p _)).grade
 have he(i): P (F i)=crustP i*b:=by unfold P; simp [Pi.single_apply,hf.eq_iff]
 have ht(i) (h:i∉ D):P i=0:=by
    unfold P; refine sum_eq_zero fun k _=> Pi.single_eq_of_ne (show i≠F k from fun g=> h (mem_image.mpr ⟨k,mem_univ _,g.symm⟩)) _
 refine ⟨fun U V i'=>congrArg _ (show seed_k x y (A U)=seed_k x y (A V) from congrArg _ (v.live U V i')),fun i=>hearthP_t _ _ _ h t, (bright_H x y|>.comp v.swift).measurable,fun i g=>?_ ,P,fun i=>?_ , fun V H T=>?_,?_⟩
 · exact (congrArg pulseH (shiftP x y (A i) _ g (e i g)).symm).trans (pulse_φ ..)
 · unfold P; exact sum_nonneg fun k _=>by rw [Pi.single_apply]; split; exact hp _; exact le_rfl
 · by_cases p':T∈D; swap
   · rw [ht T p']; have hy(U): crumb (pulseH (seed_k x y (A U))).val T=0:= zone_loc _ _ _ _ (fun i g=> p' (g.symm ▸ mem_image.mpr ⟨i,mem_univ _,rfl⟩)); simp only [hy]; exact Prism.hail (show ‖(0:ℂ)‖≤0 by simp)
   obtain ⟨i,pI,rfl⟩:= Finset.mem_image.mp p'
   let a:=Moto.hailV x i.1; let d:=Moto.hailV y i.2; let f(U):=Whig a d * (A U) i.1 i.2; have hx(U): crumb (pulseH (seed_k x y (A U))).val (F i)=f U:=by unfold F; rw [poke_f,seed_k,Matrix.of_apply, if_pos (show x=(Moto.hailV x i.1).1.1 ∧ y=(Moto.hailV y i.2).1.1 from ⟨rfl,rfl⟩),mul_comm]; rfl
   have hu:Housing.Haw p o (Pax o) f (P (F i)):= by rw [he,show crustP i*b= (‖Whig a d‖*crustP i)*b from (by rw [whig_1,one_mul])]; exact Cargo x y A b p o v .. -- tune dots
   simp_rw [hx]; exact hu.rends V H
 let Z(i):=tariff p o q i*P i;
 change ∑ i:Finset (Dwell n),Z i ≤ _; rw [←sum_subset (s₁:=D) (subset_univ _) (fun i _ w=>by unfold Z; rw [ht i w,mul_zero]),sum_image hf.injOn]
 have hv(k:Site n)(h:node k∈Pax o): separation o (node k)≤24:=by obtain ⟨j,p,v⟩:= halo_spec.mp h; rw [mem_singleton.mp p] at v; exact v -- halo orientation
 apply (sum_le_sum (g:=fun i=> ((25:ℝ)^3*q^2)*(crustP i*b)) _).trans; · rw [← mul_sum, ←sum_mul]; unfold CargoMax; apply le_of_eq; ring
 intro i _; apply mul_le_mul
 · have hx:endL o (F i)≤24:=by
      unfold endL; refine Finset.sup_le (fun k e=>?_); rcases Finset.mem_insert.mp e with rfl|q0
      · exact hv _ h -- tune k
      rw [mem_singleton.mp q0]; exact hv _ t
   unfold tariff; rw [show (F i).card=2 from (by simp [F,Haro.tray])]; apply mul_le_mul_of_nonneg_right _ (sq_nonneg _); refine (pow_le_pow_left₀ (by positivity) (b:=25) ?_ p.power).trans (pow_le_pow_right₀ (by norm_num) u); norm_cast; omega -- tune
 · exact (he i).le
 · rw [he]; exact hp i
 positivity
end Layout
end Lenten
end YM.CF.TableF
end
