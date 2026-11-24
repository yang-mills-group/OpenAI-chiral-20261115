import YM.SU5.FiniteGaugeData.Jadot.Verna
import YM.SU5.FiniteGaugeData.Cuprite.Spiny -- tune
/-! # Doppler. This is the ONE pre-heat choice. Reality of eigen densities used via selfadjointness rather than parity approximations. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 600000
set_option linter.flexible false
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Window.Presidio
open Parcel.Tanin Fock Fock.Reduction Reduction.Hutch Reduction.Drama Reduction.Drama.Pack Reduction.Jersey -- tune resolution
open Reduction.Dinar Reduction.Rheims Reduction.Verna Reduction.Dijon
open Next.Free Function Filter NormedSpace Lattice Laurent Bloch Wilson Precision Tree Finset Exterior
open Lat Rush Cube Scroll SU Peaks Dial Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Pec Cour Fir Ember Aroma Cascade Gall
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
namespace Menton
variable {N : Side}{k:ℕ}{d b:ℝ}{M:Male}
local notation "Φ" => love N
local notation "Φ⁻" => (love N).symm
local notation "R"=> (spar k M (1:Bkg (More N)))
local notation "Θ"=> tickA N
local notation "Ξ"=> ampleR k N M
local notation "Θ'"=> spring (tickA N) (ampleR k N M)
local notation "Caso"=>Op (coneA Slot)
local notation "Tovo"=> Op (Tx N Slot)
local notation "gill"=> Site N → Op (coneA Slot) -- tune precedence
abbrev grain (A:Site N → Op (coneA Slot)) : Op (Single N):= love N (subHub A)
variable {Y X:Op (Single N)} {A B:Site N → Op (coneA Slot)} -- tune
namespace grain
lemma stem (A:gill) : star (grain A)=grain (star A):=by unfold grain; rw [←map_star, subhub_star]; rfl -- tune
lemma lignite (A B:gill) : grain (A*B)=grain A*grain B:=by unfold grain; rw [←map_mul]; exact congrArg (love N) (lung (Equiv.refl _) A B).symm
lemma hanker : Injective (@grain N):=fun _ _ h=> hubfaith (Equiv.refl _) _ _ ((love N).injective h)
lemma unitC : grain (1:gill)=1:=by unfold grain; rw [show subHub (1:gill)=1 from unitHub,map_one]
lemma gain (A B:gill): grain (A-B)=grain A - grain B:=by unfold grain; rw [←map_sub, hubgap]
lemma weal (h:0≤A):0≤grain A:=by
 let B(i:Site N):Caso:= ReflW (A i); have he:A=B*star B:=by
    funext i; change A i=B i*star (B i); rw [show star (B i)=B i from refl_star (h i),show B i*B i=A i from refl_sq (h i)] -- tune h: non all? Pi.nonneg
 rw [he,lignite,←stem]; exact mul_star_self_nonneg _
lemma plained(h:A≤B):grain A≤ grain B:= sub_nonneg.mp (by rw [←gain]; exact weal (sub_nonneg.mpr h))
lemma foil (A:gill)(p:0≤grain A) (i:Site N): IsSelfAdjoint (A i):=by
 apply congrFun (f:=star A) ?_ i; apply hanker; rw [← stem]; exact IsSelfAdjoint.of_nonneg p -- syntax
abbrev cake (r:Site N →ℝ):= grain (fun i=>Canon (coneA Slot) (r i))
lemma cake_prod(r s:Site N→ℝ): cake r * cake s= cake (r*s):=by unfold cake; rw [←lignite]; apply congrArg grain; funext i; change Canon (coneA Slot) (r i)*Canon (coneA Slot) (s i)=Canon (coneA Slot) (r i*s i); rw [canon_left]; unfold Canon; rw [smul_smul]
lemma cake_co (f:Site N→ℝ)(A:gill): Commute (cake f) (grain A):=by
 show cake f*grain A = _; unfold cake; rw [←lignite,←lignite]; apply congrArg grain; funext i; change Canon _ (f i)*A i= A i*Canon _ (f i); rw [canon_left]; unfold Canon; rw [Algebra.mul_smul_comm, mul_one]
lemma cake_cub(r:Site N→ℝ): cake r^3=cake (fun i=> (r i)^3):=by rw [pow_succ (cake r) 2,sq,cake_prod,cake_prod]; exact congrArg cake (funext fun i=>by change r i*r i*r i=_; ring)
-- from light_year WP17:
private lemma xray_i(A:Site N→Op (coneA Slot))(x:Site N)(k:coneA Slot): subHub A (x,k) (x,k)= ((N.val:ℂ)^4)⁻¹ * (∑ i:Site N,A i k k):=by
 let U:=spatialU N Slot; have h(i:Site N): Fourier N x i *star (Fourier N x i)= ((N.val:ℂ)^4)⁻¹:=by unfold Fourier; simp only [Matrix.of_apply,star_div₀]; rw [div_mul_div_comm, mul_comm (frequency i x),frequency_unit]; unfold normF; simp only [star_pow,star_natCast,one_div]; ring
 let C:=jump (Equiv.refl (Site N)) A; unfold subHub hub; rw [twist_formula]; change (U.val*C*star U.val:Cab Slot N) (x,k) (x,k)= _; rw [Matrix.mul_apply]; unfold Tx; rw [Fintype.sum_prod_type, mul_sum]; apply sum_congr rfl; intro i _
 have hy (j:Site N)(v w:coneA Slot): U.val (x,v) (j,w) = if v=w then Fourier N x j else 0:=by simp only [U,spatialU,Matrix.kroneckerMap_apply,Matrix.one_apply,mul_ite,mul_one,mul_zero]
 have hh (l:coneA Slot): (U.val*C) (x,k) (i,l)=Fourier N x i * A i k l:=by
    rw [Matrix.mul_apply]; unfold Tx; rw [Fintype.sum_prod_type]; unfold C; simp only [jump_apply,Equiv.refl_apply,ite_mul,mul_ite,zero_mul,mul_zero,hy]; rw [sum_eq_single i]; · simp only [ite_true,sum_ite_eq,mem_univ]
    · intro j _ g; simp [g]
    simp
 rw [sum_eq_single k]; · rw [hh]; change _ * star (U.val _ _)=_; rw [hy,if_pos rfl,mul_right_comm,h]
 · intro j _ e; change _*star (U.val (x,k) (i,j))= _; rw [hy,if_neg e.symm,star_zero,mul_zero]
 simp
-- identity in Love; pow form retained.
lemma cake_helix(r:Site N→ℝ)(i:Single N): (cake r i i).re = ((N.val:ℝ)^4)⁻¹ *∑ z,r z:=by
 let e:= Tulip.helix N; let B(x:Site N):Caso:= Canon (coneA Slot) (r x); let T:= cake r; have he(x:Site N)(p:coneA Slot): B x p p=r x:=by unfold B Canon; rw [Matrix.smul_apply,Matrix.one_apply_eq]; simp -- name tune
 have ht:T i i=subHub B (e i) (e i):= rfl
 change (T i i).re=_; let V:= (N.val:ℝ); rw [ht]; change (subHub B ((e i).1,(e i).2) _).re=_; rw [xray_i]; -- same defin?
 simp_rw [he]; rw [←Complex.ofReal_sum,← Complex.ofReal_natCast,←Complex.ofReal_pow,←Complex.ofReal_inv,←Complex.ofReal_mul]; rfl -- tune
end grain
abbrev senate (k:ℕ)(M:Tulip.Male)(i:Site N):= sparseA k M i + (1-bins Slot)
variable (p:1≤k)
include p
lemma YAM : Θ'⁻¹=grain (senate k M):=by
 let A:=subHub (fun _:Site N=>bins Slot); let B:gill:=1 -- ambiguity
 have he: subHub B - A=subHub (B-fun _=> bins Slot):=hubgap ..
 have h:1-A=subHub (B-fun _=>bins Slot):= by rwa [show subHub B=1 from unitHub] at he
 apply Φ⁻.injective; change Φ⁻ (spring (tickA N) (ampleR k N M))⁻¹=Φ⁻ (grain (senate k M)); unfold grain; rw [StarAlgEquiv.symm_apply_apply,year_inv p,show flatV Slot N=A from bin_hub.symm,h]; exact hubsum (Equiv.refl _) _ _
-- Q & Qc*... fluid. only.
lemma Merch(r:Site N→ℝ) : Commute (Θ*R*(1-Θ)) (grain.cake r):=by
 have ht: Ξ= grain (fun i=> fuel Slot k M.val (mel i)):=by
    apply Φ⁻.injective; change Φ⁻ (ampleR k N M)=Φ⁻ (grain _); unfold grain; rw [StarAlgEquiv.symm_apply_apply]; rw [show Ξ= grace k M (0:Dress N) 0 from ?_]; exact base_grace p M (0:Dress N) rfl
    unfold ampleR grace postR; simp [Crops,capT]
 have hh: Θ=grain (fun _=> bins Slot):=by unfold grain; rw [bin_hub]; exact plusInk N
 change Commute (Ξ*(1-Θ)) _; rw [ht,hh,← grain.unitC (N:=N),←grain.gain,←grain.lignite]; exact (grain.cake_co r _).symm
-- plan earning. Explicit.Cube costs.
omit p in
private lemma sugar_io {x:ℝ}(e:0≤x)(t:1≤b) : (1+b*x)^3≤ (1+b)^3*(1+x^3):=by
 rcases le_total x 1 with h|h
 · refine le_trans (b:=(1+b)^3) (pow_le_pow_left₀ (by positivity) (by linarith only [mul_le_mul_of_nonneg_left h (zero_le_one.trans t)]) 3) ?_; exact le_mul_of_one_le_right (by positivity) (by nlinarith only [pow_nonneg e 3]) -- positivity uses t
 · calc
      _ ≤ ((1+b)*x)^3:= pow_le_pow_left₀ (by positivity) (by linarith) 3
      _ ≤ _:=by rw [mul_pow]; exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (by positivity)
lemma annual : ∃ b:ℝ,0≤b ∧ ∃ N₀:ℕ,∀ N:Side,N₀≤ N.val→Even N.val→∀ M:Tulip.Male, let P:= spar k M (1:Bkg (More N)); IsStarProjection P → ∃ W:Op (Single N), Booster (tickA N) P W b:=by
 obtain ⟨C,h,N₀,H⟩:= Cascade.sugar; obtain ⟨c,hc,hQ⟩:= Cascade.chillY k p; let b:=1+c; have he:1≤b:=by unfold b; linarith only [hc]
 let d:= (1+b)^3; have hb:0<b:= lt_of_lt_of_le zero_lt_one he; have hd:0≤d:=by unfold d; positivity
 refine ⟨d*(1+C),by positivity,N₀,?_⟩; intro N v g M P u
 let Q:=tickA N; let X:= spring Q (Q*P); let T:= X⁻¹; let x(i:Site N):= ‖bark i‖⁻¹; have ht(i:Site N):0≤x i:=by unfold x; positivity
 let r(i:Site N):=1+b*x i; have hr(i):1≤r i:=le_add_of_nonneg_right (mul_nonneg hb.le (ht i))
 let W:= grain.cake r; have hw:1≤W:=by rw [←grain.unitC (N:=N)]; apply grain.plained; intro i; change 1≤Canon _ (r i); rw [canon_map]; exact (map_one _).symm.trans_le (algebraMap_mono _ (hr i)) -- tune W def
 let B:=senate (N:=N) k M; have hy:T=grain B:=YAM p; have hy':Rheims.frost Q P 0=X:= bloom_zero ..; refine ⟨W,plus_P _,u,hy'.symm ▸ (iceT (N:=N) (M:=M) p),?_,?_,hw,Merch p _,?_,by positivity⟩
 · rw [show Rheims.frost (tickA N) P 0= _ from hy', show X⁻¹=grain B from hy]; unfold W; rw [grain.cake_prod]; apply grain.plained; intro i; have hu:IsStarProjection (bins Slot):= ⟨binsSq _,binsAdj _⟩
   have hk: ‖sparseA k M i‖≤c*(x i)^2:= by
       apply (le_of_le_of_eq _ (b:=c*(‖bark i‖^2)⁻¹) (by unfold x; rw [inv_pow])); unfold sparseA edgeH; rw [norm_smul]; exact (mul_le_of_le_one_right (norm_nonneg _) (hu.norm_le _)).trans (hQ M N i)
   have hp:‖B i‖ ≤ r i*r i:= (norm_add_le ..).trans ((add_le_add hk (hu.one_sub.norm_le _)).trans (by
     unfold r b; have he:c≤(1+c)*(1+c):=by nlinarith only [sq_nonneg c,hc]
     nlinarith only [mul_nonneg hc.le (ht i),ht i,mul_le_mul_of_nonneg_right he (sq_nonneg (x i))])) -- tune
   change B i ≤Canon _ (r i*r i); rw [canon_map]; refine (grain.foil B (hy ▸ (lit_inv (show lit X from iceT p)).1) i).le_algebraMap_norm_self.trans (algebraMap_mono _ hp) -- ∃type lemma expects matrix.Op. hy type. syntax
 · change Commute (Rheims.frost Q P 0)⁻¹ W; rw [hy', show X⁻¹=grain B from hy]; exact (grain.cake_co ..).symm
 intro i; unfold W; rw [grain.cake_cub, grain.cake_helix]; apply (inv_mul_le_iff₀ (pow_pos (nPos N) 4)).mpr
 apply (sum_le_sum (s:=univ) (fun (i:Site N) _=> sugar_io (ht i) he)).trans; unfold x; simp_rw [inv_pow]; rw [← mul_sum,sum_add_distrib,sum_const,card_univ,site_card,nsmul_eq_mul,mul_one,Nat.cast_pow]; change d*(_ + ∑ i:Site N,(‖bark i‖ ^ 3)⁻¹) ≤ _; nlinarith only [mul_le_mul_of_nonneg_left (H N v g) hd] -- tune association
-- thresholds pinned before Discovery
abbrev FixB(k:ℕ)(p:1≤k):=(annual p).choose
abbrev FixN(k:ℕ)(p:1≤k):=(annual p).choose_spec.2.choose
lemma fixp(k:ℕ)(p:1≤k):0≤FixB k p:= (annual p).choose_spec.1 -- include p duplicated note
lemma fixe(h:FixN k p≤N.val)(e:Even N.val)(g:IsStarProjection R): ∃ X:Op (Single N), Booster (tickA N) (spar k M (1:Bkg (More N))) X (FixB k p):= (annual p).choose_spec.2.choose_spec N h e M g
end Menton
end YM.CF.Window.Presidio
