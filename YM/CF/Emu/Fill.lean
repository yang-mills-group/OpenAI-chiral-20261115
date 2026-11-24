import YM.CF.Emu.Rhyme
set_option autoImplicit false
noncomputable section
namespace YM.CF.Emu
open YM.CF.Onyx
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill Kea Flare Rush Tulip Cube Fock SU Dial Thera
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {N:Side}{j:ℕ}{M:Jill.Male}{R:ℝ}{d:Candle}
-- generated legs. path order may vary arbitrarily. common base o.
structure Wing where
 a : SpinIdx
 x : Slot
 ord : Lattice.Order
def hub(a: Wing)(o:Site N)(z:Cover): Single N:=((o+wrap N z,a.a),a.x)
def stemF(o:Site N)(z:Cover)(a:Wing)(U:Bkg (More N))(h:E): E := (travel U (node o) (leap z a.ord))⁻¹*h
-- embed
abbrev cote(K:UNI Slot):UNI (Single N):=⟨jump (Equiv.refl _) (fun _=>K.val),jump_unitary _ _ (fun _=>K.property)⟩
def hint(o:Site N)(z:Cover)(a:Wing)(U:Bkg (More N))(h:E):Ket (Single N) := wind o z • acts (cote (matter (stemF o z a U h))).val (basisKet (hub a o z))
lemma hail(o:Site N)(z:Cover)(a:Wing)(U:Bkg (More N))(h:E): ‖hint o z a U h‖=1:=by
 unfold hint; rw [norm_smul, show ‖wind o z‖=1 from fee_norm _,one_mul,act_unit_norm]; simp [basisKet] -- tune
lemma cue (a b: UNI Slot) : (cote (N:=N) (a*b)).val=(cote a).val*(cote b).val:=by simp only [cote,jump_mul,Equiv.refl_apply,Equiv.refl_trans]; rfl
lemma step_q(a:Wing)(o:Site N)(z: Cover)(U:Bkg (More N))(t:Site (More N)→E)(p:E): stemF o z a (gauge t U) (t (node o)*p)= t (node (hub a o z).1.1)*stemF o z a U p:=by
 unfold stemF; rw [travel_gauge, leap_end]; change _= t (node (o+wrap _ _))*_; group
lemma tint(o:Site N)(z:Cover)(a:Wing)(k:E): acts (cote (matter k)).val (basisKet (hub a o z))=∑ i:Slot,(matter k).val i a.x • basisKet ((hub a o z).1,i):=by
 let A:=hub a o z; apply PiLp.ext; intro j; rw [basis_act]; simp only [WithLp.ofLp_sum,Finset.sum_apply,basis_apply,ite_true,WithLp.ofLp_smul,Pi.smul_apply, smul_eq_mul, mul_ite,mul_one,mul_zero]; rcases j with ⟨j,i⟩; -- tune
 rw [sum_eq_single i]; swap; · intro m _ e; rw [if_neg (fun w=>e (Prod.mk.inj w).2.symm)]
 swap; · simp
 change jump _ _ _ _=_; rw [jump_apply]; simp only [Equiv.refl_apply,Prod.mk.injEq, and_self,and_true,eq_self]; rfl -- inspect
lemma hike(o:Site N)(z:Cover)(a:Wing)(U:Bkg (More N))(p:E)(t:Site (More N)→ E): hint o z a (gauge t U) (t (node o)*p)= acts (tradew N t).val (hint o z a U p):=by
 have hp(x: Single N): acts (cote (N:=N) (matter (t (node x.1.1)))).val (basisKet x)=acts (tradew N t).val (basisKet x):=by
    apply PiLp.ext; intro y; rw [basis_act,basis_act]; unfold cote tradew; simp only [jump_apply,Equiv.refl_apply]; split_ifs with h; swap; rfl; rw [show y.1=x.1 from h]
 let x:=hub a o z; let b:= stemF o z a U p; unfold hint; rw [step_q,map_mul,cue,act_mul,map_smul]; rw [tint,map_sum,map_sum]; apply congrArg; apply sum_congr rfl; intro j _; rw [map_smul,map_smul]; exact congrArg ((matter b).val j a.x • ·) (hp (x.1,j))
lemma tax_f(o:Site N)(z:Cover)(a:Wing)(d:Candle): hint o z a (Kea.tax d) 1=(wind o z*star (newm d z a.x)) • basisKet (hub a o z):=by
 unfold hint; rw [tint, stemF]; simp_rw [mul_one,map_inv]; have he:= keen (N:=N) d z o a.ord; rw [track_pr] at he
 rw [sum_eq_single a.x]; swap; · intro i _ v; change star ((matter _).val) i _ • _=_; rw [show (matter _).val = _ from he, Matrix.star_apply, Matrix.diagonal_apply_ne _ v.symm,star_zero,zero_smul]
 swap; · simp
 change wind o z • (star ((matter _).val) _ _ • _)= _; rw [show (matter _).val = _ from he,Matrix.star_apply,Matrix.diagonal_apply_eq,smul_smul]; rfl
lemma wing_m (x y:Single N):tickA N x y=if x=y ∧ x.1.2∈plusHalf then 1 else 0:=by
 change cutM _ (helix N x) (helix N y) = _; rw [cutM, Matrix.diagonal_apply]; simp [upperP,helix, Matrix.diagonal_apply]; grind -- tune order
-- false create bar from plus, true remove (-) from minus
def signW(a:Wing): Bool := decide (a.a ∉plusHalf)
lemma hinge (o:Site N)(z:Cover)(a:Wing)(U:Bkg (More N))(p:E): acts (tickA N) (hint o z a U p)= if signW a then 0 else hint o z a U p:=by
 have he(i:Slot):acts (tickA N) (basisKet ((hub a o z).1,i))= if signW a then 0 else basisKet ((hub a o z).1,i):=by
    apply PiLp.ext; intro j; rw [basis_act,wing_m]; by_cases h:j=((hub a o z).1,i) <;> by_cases l: a.a∈plusHalf<;> first|simp only [h]; simp [hub,basis_apply,signW,h,l]|simp [h,l,signW,basis_apply]
    exact h
 unfold hint; rw [tint,map_smul,map_sum]; simp_rw [map_smul,he]; split_ifs with u; simp; rfl -- tune
end YM.CF.Emu
