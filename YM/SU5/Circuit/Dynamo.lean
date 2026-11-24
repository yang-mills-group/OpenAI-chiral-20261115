/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.SU5.Circuit.Hector
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Regis.Circuit
open Function Filter Metric Lattice Laurent Next.Free Bloch Finset CF CF.Lat CF.Jill CF.Ember CF.Flare CF.Onyx CF.Fir
open Precision Exterior Matrix RG Work.F06
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix
/-! # Uniform analytic estimates for damped complement symbol on *actual* momenta. -/
variable {ι β m l s:Type*}[Fintype m][Fintype l][Fintype s][DecidableEq m][DecidableEq l][DecidableEq s]
def Actus (T:Ember.Tax ι)(p:ℤ)(f:ι→ℂ→Matrix m l ℂ):=∀ i j, CF.Ember.Act T p (fun z u=>f z u i j)
variable {T:CF.Ember.Tax ι}{p q:ℤ}
namespace Actus
variable {f g:ι→ℂ→ Matrix m l ℂ}(h:Actus T p f)
lemma comp (h:Actus T p f){w:ι→ℂ→Matrix l s ℂ}(d:Actus T q w):Actus T (p+q) fun i z=> f i z*w i z:=by intro x y; simp_rw [Matrix.mul_apply]; exact Act.finiteSum univ _ fun j _=> (h x j).mul (d j y)
lemma shift (h:Actus T p f)(k:Actus T p g): Actus T p fun i z=> f i z+g i z:=fun i j=> (h i j).add (k i j)
lemma scale (h:Actus T p f){s:ι→ℂ→ℂ}(k:Act T q s):Actus T (q+p) fun i z=> (s i z) • f i z:=fun i j=> k.mul (h i j)
lemma power {p:β→ι→ℂ→ℂ}(F: Finset β)(v:∀ i∈F,Act T 0 (p i)): Act T 0 fun i x=>∏ j∈F,p j i x:=by
 classical
 induction F using Finset.induction_on with
 | empty=> simpa only [Finset.prod_empty] using Act.anchor T (1:ℂ)
 | @insert i S h ih=> simp_rw [Finset.prod_insert h]; exact (v i (mem_insert_self ..)).mul (ih fun j h'=> v j (mem_insert_of_mem h'))
lemma déterminant (A:ι→ℂ→Matrix m m ℂ)(h:Actus T 0 A): Act T 0 fun i z=> (A i z).det:=by
 simp only [Matrix.det_apply]; apply Act.finiteSum univ; intro e _
 have ht:= power (p:=fun j i z=> (A i z) (e j) j) univ (fun j _=>h (e j) j)
 rcases Int.units_eq_one_or e.sign with g|g
 · simpa only [g,one_smul] using ht
 simpa only [g,Units.neg_smul,one_smul] using ht.neg
lemma adjunct {A:ι→ℂ→Matrix m m ℂ}(h:Actus T 0 A):Actus T 0 fun i z=> (A i z).adjugate:=by
 intro a b; simp only [Matrix.adjugate_apply]
 apply déterminant; intro i j; by_cases e:i=b
 · simp only [e,Matrix.updateRow_self]; exact Act.anchor T _
 simp only [Matrix.updateRow_ne e]; exact h i j
lemma counter {A:ι→ℂ→Matrix m m ℂ}(h:Actus T 0 A)(c:ℝ)(p:0<c)(u:∀ i,c≤‖(A i 0).det‖):Actus T 0 fun i z=> (A i z)⁻¹ :=by
 have hp:= Act.inv (déterminant A h) ⟨c,p,fun i=> by simpa using u i⟩
 have hv:= scale (adjunct h) hp
 intro i j; simp_rw [Matrix.inv_def, Ring.inverse_eq_inv]; exact hv i j
lemma inverseCall (A:Matrix m m ℂ)(r:ℂ)(hr:r≠0): (r•A)⁻¹ = r⁻¹ • A⁻¹:=by
 by_cases e:IsUnit A.det
 · letI:= invertibleOfNonzero hr; rw [Matrix.inv_smul A _ e,invOf_eq_inv]
 rw [Matrix.nonsing_inv_apply_not_isUnit,Matrix.nonsing_inv_apply_not_isUnit _ e,smul_zero]
 rw [Matrix.det_smul]; simp at e; simp [e]
lemma coin (T:CF.Ember.Tax ι)(p:ℤ):Act T p (fun i _=> (T.r i:ℂ)^p):=⟨1,1,one_pos,one_pos,fun i z h=>⟨differentiableAt_const _,by simp [Real.norm_of_nonneg (T.pos i).le]⟩⟩
end Actus
variable {N:Side}{M:Bed}{Q:Clip}{σ η C:ℝ}{i:Site N}
structure Topaz (Q:Clip)(σ η C:ℝ) where
 N:Side
 M:Bed
 L:Floor M Q N η C
 a:M.covered σ C
 hn:Even N.val
 i:Site N
 e:0<‖ruby i‖
 y:ℝ -- tail cost
 yH:0<y
namespace Topaz
abbrev path(T:Topaz Q σ η C):=ruby T.i
abbrev G (Q:Clip)(σ η C:ℝ): CF.Ember.Tax (Topaz Q σ η C):=⟨fun i=> ‖i.path‖,Real.pi, fun i=> i.e,fun i=>orb _ _ i.hn⟩
local notation "g"=>G Q σ η C
abbrev hop (i:Topaz Q σ η C)(a:Axis)(z:ℂ):= rubyM i.i + spark a (raf g i z)
lemma revolve (a:Axis):Move g fun i z=> i.hop a z:=Move.add (go_b path (fun _=>rfl) (fun i=>orb _ _ i.hn)) (sparkBud _ (raft ..) a) (fun i=> by simp [raf,spark])
end Topaz
variable {U:ι→ℂ→ Momentum}(H:Move T U)
include H
lemma west : Move T (fun i z=> -U i z):=⟨H.act.neg,fun a h=>(H.hit a h).imp fun b ⟨hv,B⟩=>⟨hv,fun i z hz=> cube_neg _ (B i z hz)⟩⟩
lemma spirited (a:Axis):Act T 1 fun i z=> seedQ 1 (U i z) a:= H.freeze (seed_control (fun _=>1) (fun _=>a)) (fun i=>by simp [seedQ,narrow,chip])
lemma sprint (n:ℕ): Actus T 1 fun i z=>signal 1 n (U i z):=by
 intro i j; have ht:=Act.finiteSum univ (fun a x z=> seedQ 1 (U x z) a * (Exterior.left ℂ n a i j)) (fun a _ => (spirited H a).mul (Act.anchor T _)); simpa [signal,wedge,Matrix.sum_apply,seedQ,tripQ,narrow] using ht
lemma abroad (n:ℕ): Actus T 1 fun i z=>mirage 1 n (U i z):=fun i j=>sprint (west H) n j i
lemma lustrous : Act T 2 fun i z=> divisor 1 (U i z):= Act.finiteSum univ _ (fun i _=> (spirited H i).mul (spirited (west H) i))
omit H
lemma route (h:0<σ)(v:0<C)(a:Axis):Actus (Topaz.G Q σ η C) 2 fun i z=> cliffMap i.M (i.hop a z):=by
 let t:=Topaz.G Q σ η C; have hq:Actus t 0 (fun i z=>i.M.metric.read (i.hop a z)):=by
   let W(i:Topaz Q σ η C):= i.M.metric; have he:Stock (fun _:Topaz Q σ η C=>1) (α:=fun _=>TypeFace 2) (β:=fun _=>TypeFace 2) W:=⟨fun _=>zero_le_one,σ,C,h,v,fun i=>by rw [mul_one]; exact i.a.2.1⟩
   exact fun i j=> (Topaz.revolve a).plunge ((price_reads he).tap i j)
 have H:=Topaz.revolve (Q:=Q) (σ:=σ) (η:=η) (C:=C) a; exact Actus.shift (Actus.comp (Actus.comp (abroad H 1) hq) (sprint H 1)) (Actus.comp (sprint H 0) (abroad H 0))
lemma crystal (h:0<σ)(v:0<C)(a:Axis):Actus (Topaz.G Q σ η C) (-2) fun i z=> (cliffMap i.M (i.hop a z))⁻¹:=by
 let t:=Topaz.G Q σ η C; let r(i:Topaz Q σ η C):ℂ:= (t.r i:ℂ)^(-2:ℤ); let X(i:Topaz Q σ η C)(z:ℂ):= cliffMap i.M (i.hop a z); let A(i:Topaz Q σ η C)(z:ℂ):= r i • X i z
 have he:Actus t 0 A:= Actus.scale (route h v a) (Actus.coin t (-2))
 have hz:Actus t 0 (fun i z=> (A i z)⁻¹):=by
   refine Actus.counter he _ (show 0<aimRock Q^4 from pow_pos (aimed _) _) fun i=> ?_
   have hv:= det_fort i.L i.a h i.i i.hn i.e; have hP:=t.pos i; change _ * (t.r i)^8≤_ at hv; unfold A; rw [Matrix.det_smul,norm_mul,norm_pow]; unfold r; rw [norm_zpow, Complex.norm_real,Real.norm_of_nonneg hP.le]; unfold X Topaz.hop; simp only [raf,mul_zero,spark,zero_smul,add_zero,show Fintype.card (TypeFace 1)=4 from (Fintype.card_congr axisEquiv).symm]; exact (le_of_eq (by field_simp : aimRock Q^4=(t.r i ^ (-2:ℤ))^4*(aimRock Q^4*(t.r i)^8))).trans (mul_le_mul_of_nonneg_left hv (by positivity)) -- tune
 have hx:= Actus.scale hz (Actus.coin t (-2)); change Actus t ((-2) + 0) (fun i z=> r i • (A i z)⁻¹) at hx
 have hw(i):r i≠0:= zpow_ne_zero _ (by exact_mod_cast (t.pos i).ne')
 simp_rw [A, Actus.inverseCall _ _ (hw _),smul_inv_smul₀ (hw _)] at hx; exact hx
lemma costume(h:0<σ)(v:0<C)(a:Axis):Actus (Topaz.G Q σ η C) 0 fun i z=> Cov i.M (i.hop a z):= Actus.comp (Actus.comp (sprint (Topaz.revolve a) 1) (crystal h v a)) (abroad (Topaz.revolve a) 1)
def cusp (M:Bed)(v:ℝ)(p:Momentum):orbC:= damp v (divisor 1 p) • Cov M p
lemma pivotal (h:0<σ)(v:0<C)(a:Axis):Actus (Topaz.G Q σ η C) 2 fun i z=> cusp i.M i.y (i.hop a z):= by
 let t:=Topaz.G Q σ η C; refine Actus.scale (costume h v a) (q:=2) (thin _ (lustrous (Topaz.revolve a)) ⟨_,pow_pos Next.Free.meter.low_pos 2,?_⟩ _ (fun i=>i.yH)); intro i; change _ * (t.r i)^2≤_; unfold Topaz.hop; simp only [raf,mul_zero,spark,zero_smul,add_zero]; exact (mul_le_mul_of_nonneg_left (abut i.path) (sq_nonneg _)).trans (divisor_real_bounds 1 (ruby_spin i.i i.hn)).1
end YM.Regis.Circuit
#print axioms YM.Regis.Circuit.pivotal
