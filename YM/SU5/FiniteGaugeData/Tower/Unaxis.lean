import YM.SU5.FiniteGaugeData.Tower.Central
/-!
# Uniform drive consumer. Finite periods only. Using all-aligned-origin
hypothesis would require paying pure price across levels even at non-scaled
positions. Thus choose origins as integer *multiple of w*! Includes 0,
closed under the internal-seam operation and later applies with pure prices
paid there by origins at coarse registration.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 270000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Heat Analysis
section train
variable {K:Calibration}{m:Side}{L:Loom (K.c m)}{Y:Mark (K.c m)→ℂ}{B:ℝ}(p:Metered K m L Y B)
variable (j: Axis)(w:ℤ)
variable {F X:Family K}{f x:Finset Cover}(e:0 < w)(u:InTest K true f false F)(h:Between K j 0 (ruler K.B*w) f)(t:InTest K true x false X)(A:ℤ)(v:Between K j (2*(ruler K.B*w)) A x)(z:0≤ A)
local notation "c"=> (K.c m).val
variable (N:ℕ) (D:ℝ)(d:ℕ)
noncomputable def wages (Z:Calibration)(B : ℝ)(d:ℕ)(A:ℤ)(k:ℝ):= (1+closefare Z B (rim_width A d)+closefare Z B d)*(1+k^4+k^2)
local notation "K₀" k:max=> wages K B d A k
local notation "φ" n:max x:max=> worth (m:=m) Y j w F X n x
include p e t u
lemma receives (i k:ℝ)(hF:pay F i)(hX:pay X k)(a0:CompactArc x d):
 BddAbove (Set.range fun v':ℤ=> φ N (w*v')) ∧
 (widthPair K d+ addgap K≤c→ ∀ v':ℤ,φ 0 v' ≤ K₀ k):=by
 constructor
 · use principal (m:=m) Y j w F X N
   rintro _ ⟨v',rfl⟩; exact housing p j w (w * v') u t i k hF hX
 intro h v'
 have he:=single_hire p j w v' (f:=F) X a0 t k hX h
 have pD:0 ≤ closefare K B d:=(Real.exp_pos _).le
 have hc:0≤closefare K B (rim_width A d):=(Real.exp_pos _).le
 refine he.trans ?_
 unfold wages; nlinarith [Real.exp_pos 1, mul_nonneg hc (pow_nonneg (pay_nonneg hX) 4),mul_nonneg pD (pow_nonneg (pay_nonneg hX) 4),mul_nonneg hc (sq_nonneg k)]
include v z
local notation "b"=> ruler K.B*w -- careful w var
lemma last_entry {k:ℝ}(hX:pay X k)(a0:CompactArc x d)(hl:widthPair K (rim_width A d)+addgap K ≤ c)
 (l₀:2*(ruler K.B*w*N)≤ (c:ℤ))(l₁:(c:ℤ) ≤2*(ruler K.B*w*N)+2*(ruler K.B*w))
 (hA:A ≤ (c:ℤ))(i:ℤ): ‖Y ((rungMinus j w (w*i) N X * rungPlus j w (w*i) N X) m)‖≤ (K₀ k)^2:=by
 obtain ⟨U,V⟩:=show ∃ U:Axis→ℤ,Transom j x U d by choose U V using a0; exact ⟨U,fun i _ v t=>V _ _ t⟩
 apply (both_hire p j w _ _ e t A v V z l₀ l₁ hl k hX).trans
 have pD:0 ≤ closefare K B d:=(Real.exp_pos _).le
 have hc:0≤closefare K B (rim_width A d):=(Real.exp_pos _).le
 have hk:=pay_nonneg hX
 have hs:0 < K₀ k:=by unfold wages; positivity
 let T:=K₀ k
 have ht:closefare K B (rim_width A d)*(k^2*k^2) ≤ T:=by unfold T wages; nlinarith [mul_nonneg hc (sq_nonneg k),mul_nonneg pD (pow_nonneg hk 4),mul_nonneg pD (sq_nonneg k)]
 refine ht.trans ?_
 have h':1 ≤ T:=by
    have h':0 ≤ k^4+k^2:=by positivity
    unfold T wages; nlinarith [mul_nonneg hc h',mul_nonneg pD h']
 change T≤T^2; nlinarith
include h
lemma booking (hD:0<D){k Bf:ℝ}(hX:pay X k)(hF:pay F Bf)(a0:CompactArc x d)(hl:widthPair K (rim_width A d)+addgap K ≤ c)(ht: widthPair K d+addgap K≤c)
 (l₀:2*(ruler K.B*w*N)≤ (c:ℤ))(l₁:(c:ℤ) ≤2*(ruler K.B*w*N)+2*(ruler K.B*w))
 (hJ: (b) * N+A≤(c:ℤ))(Pure:∀ i:ℤ, ‖Y (banner j w (w*i) N F m)‖ ≤ D^(2*N)): ∀ n:ℕ,n ≤ N → φ n 0 ≤ K₀ k*D^n:=by
 let q(n:ℕ):=sSup (Set.range (fun i:ℤ=>φ n (w*i)))
 have he (n i): 0 ≤ φ n i:=norm_nonneg _
 have hP(n i):φ n (w*i)≤ q n:=le_csSup ((receives p j w e u t A n d Bf k hF hX a0).1) (Set.mem_range_self i)
 have hu(n):0 ≤ q n:= (he n (w*0)).trans (hP n 0)
 have hh(n)(x:ℝ)(v:∀ i:ℤ, φ n (w*i)≤ x): q n≤ x:= csSup_le (Set.range_nonempty _) (by rintro _ ⟨i,rfl⟩; apply v)
 have hc:=ruler_gene K.B; have hk:0<K₀ k:=by unfold wages closefare; have hr:=pay_nonneg hX; positivity
 have hT:= ladder_max q N (C:=K₀ k) (B:=D) hk hD (fun i _=>hu i) (hh 0 _ (fun i=> (receives p j w e u t A 0 d Bf _ hF hX a0).2 ht _)) (show _ from ?_) (show _ from ?_)
 · exact fun n t=> le_trans (by simpa [mul_zero] using hP n 0) (hT n t)
 · apply hh
   intro i
   apply (sq_le_sq₀ (he N _) (by positivity)).mp
   rw [mul_pow,←pow_mul, Nat.mul_comm N 2]
   have h:=bastion p j w (w*i) N e u h t A v l₀ l₁ (by nlinarith)
   exact h.trans (mul_le_mul (last_entry p j w e u t A v z N d hX a0 hl l₀ l₁ (by nlinarith) i) (Pure _) (norm_nonneg _) (sq_nonneg _)) -- order/model
 intro n v'
 let g:= q (n+2)* q n; have hn:0 ≤ g:= mul_nonneg (hu _) (hu _)
 have h: q (n+1) ≤ Real.sqrt g:=by
    apply hh; intro i
    apply (Real.le_sqrt (he _ _) hn).mpr
    refine (chamber_cut p j w (w*i) e z u h t (fun i hi=>⟨(by have hx:=(v i hi).1; nlinarith), (v i hi).2⟩) (by
       change ruler K.B * (w * (n+2:ℤ))+A ≤ _
       have h': (n:ℤ)+2 ≤ (N:ℕ):=by omega
       nlinarith [mul_le_mul_of_nonneg_left h' (show 0≤b by positivity)])).trans ?_
    have hp(i':ℕ): φ i' (w*i+w) ≤ q i':=by rw [show w*i+w=w*(i+1) by ring]; exact hP ..
    exact mul_le_mul (hp (n+2)) (hp n) (norm_nonneg _) (hu _)
 have hh:= (sq_le_sq₀ (hu _) (Real.sqrt_nonneg _)).mpr h; rwa [Real.sq_sqrt hn] at hh
end train
end YM.CF.Buffered.Afterglow.Tower.SlabMark
#print axioms YM.CF.Buffered.Afterglow.Tower.SlabMark.booking
