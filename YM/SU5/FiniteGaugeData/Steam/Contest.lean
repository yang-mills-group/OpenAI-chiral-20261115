import YM.SU5.FiniteGaugeData.Steam.Repetition
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
namespace Quest
open Window.Steve
abbrev admiss (n:Side):= Face (Per (More n))
open Heat
variable {K:Calibration} {B n:Side}{t:ℝ}
def glitches (S: Support (More n))(t:ℝ)(x:Pane n):= (misses x t).filter (fun p=> touched p ⊆ S) -- use noncomp classical
set_option quotPrecheck false
def Glints (m:ℕ)(S:Support (More n))(t:ℝ)(f:Mark n):= ∀ i,f i≠0 → m ≤ (glitches S t i.1).card
local notation "N"=> More n
lemma glint_gloss (t:ℝ) (S:Support (More n))(x:Pane n)(a:Axis)(s:ℤ) : (glitches S t (fling a s n x)).card ≤ (glitches (S.image ((plane a s).anon n)) t x).card := by
 let T:Site (More n):= wrap _ (2 • (s • step a)); let u := Signed.mirror a; let f:= Face.send u T
 refine card_le_card_of_injOn f ?_ (Face.injective_send u T).injOn
 intro i p; obtain ⟨p,w⟩:= (mem_filter.mp (show i∈ glitches S t (fling _ _ _ x) from p)); refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, (show _ from lt_of_lt_of_le ((mem_filter.mp p).2) (Face.send_price x i u T SU.group.chord SU.group.chord_inv fun k g=>SU.group.chord_conj g k).le)⟩,?_⟩
 unfold f; rw [Work.H03.touched_send]; exact Finset.image_subset_image w
-- P challenge
lemma split_growth {L:Side}{k u w j:ℕ}(a:Axis)(s:ℤ)(S:Support (More n))(m:ℕ)(f:Mark n)(p:Glints m S t f)(T:S⊆ band n a s u)(g:Margin L k w j u) : Glints (m*2) (S.image ((plane a s).anon n)∪ S) t (reflMark a s f*f):= by
 intro x hx
 have he:= p x (right_ne_zero_of_mul hx); let F:= reflFields a s x
 have hp : m ≤ (glitches (S.image ((plane a s).anon n)) t x.1).card:=(p F ?_).trans (glint_gloss ..); swap
 · intro v; apply left_ne_zero_of_mul (show reflMark a s f x * f x ≠ 0 from hx); change theta _ (f F)=0; rw [v, Fock.theta_zero]
 let A:= S.image ((plane a s).anon n); have hy : Disjoint A S:= by refine Finset.disjoint_left.mpr ?_; intro y e f; have he:= margin_separate a s g y y (Finset.image_subset_image (f:=(plane a s).anon n) T e) (T f); simp at he
 change m ≤ (glitches A t _).card at hp
 apply (le_trans (by omega : m*2≤(glitches S t x.1).card+(glitches A t x.1).card) _); rw [← Finset.card_union_of_disjoint]; swap
 · refine Finset.disjoint_left.mpr (fun i e f=> Finset.disjoint_left.mp hy (((mem_filter.mp f).2) (Work.E01.base_touched _)) (((mem_filter.mp e).2) (Work.E01.base_touched _)))
 have he(B S:Support N)(u:B⊆ S):glitches B t x.1⊆ glitches S t x.1 := fun i h=>mem_filter.mpr ⟨(mem_filter.mp h).1,Subset.trans ((mem_filter.mp h).2) u⟩; exact card_le_card (Finset.union_subset (he _ _ subset_union_right) (he _ _ subset_union_left))
lemma Mirror.glints {L:Side}{k r u w j m:ℕ}{x y:Mark n}{S T:Support N}(p:Mirror B u n S x T y r)(A:Margin L k w j u)(q:Glints m S t x): Glints (m*r) T t y:=by
 induction p generalizing m with | self=> rwa [mul_one] | grow i s e=> exact split_growth i (gaugeShift B s) _ _ _ q e A | trans _ _ ih it=> simpa only [Nat.mul_assoc] using it (ih q)
open Py Py.Rate LocalLimit Preparation Steam Journey Vale
local notation "L"=> Λ.R.L
variable {Λ:Preparation}{l i s k:ℕ}{Y:Course Λ (VolumeCape.Dream.Nimbus l)}{h:Real.exp 1 ≤ Λ.x}{r:ℝ}
variable {I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→Family (tent Y h)→ℂ}{u v:ℕ→ℕ} (X:Universal Y h u v I E)(P:Club Y r s)
variable {c:ℝ}
local notation "N₀" i:max=> side Y i s
local notation "xₛ"=> hat Λ.R.L Λ.x s
local notation "γ"=> Pressure.temp xₛ
local notation "λX"=> Steam.frost Λ.K.top.clip xₛ
local notation "μ"=> (tent Y h)
local notation "σ"=> Ω
local notation "κ" k:max=>((Y.voyage i).X (Y.uv k)).gram s
include X P
-- sentinel
set_option maxHeartbeats 400000 in
lemma GlossBill {i:ℕ}{b:Mark (N₀ i)}{S:Support (More (N₀ i))}(he:0≤c)(p:∀ x,‖b x‖ ≤ c)(q:Glints 1 S (Pressure.temp (hat Λ.R.L Λ.x s)) b): setback Y s i (c * Real.exp (-(Steam.frost Λ.K.top.clip (hat Λ.R.L Λ.x s)))) S b v:=by
 intro n y T V
 let G:= (Y.voyage i)
 have hz:Glints n T γ y:= by simpa only [one_mul] using V.glints (Journey.prepared Λ l) q
 filter_upwards [X.pick.pass Y h s i] with k ht
 let pX:= P.full i (v k) ht.enters
 intro x; let F:= y ∘ drawn (G.CapeT s); let C:=Steam.τ Λ.W xₛ (N₀ i); let V₁:= (misses x.1 γ).card
 by_cases u: y (drawn (G.CapeT s) x)=0
 · change ‖inner ℂ _ (acts (y (drawn ((Y.voyage i).CapeT s) x)) _)‖≤_; rw [show y (drawn ((Y.voyage i).CapeT s) x)=0 from u,act_zero,inner_zero_right,norm_zero]; positivity
 have hs : (n:ℝ) ≤ V₁:= Nat.cast_le.mpr ((show n ≤ (glitches T γ x.1).card from hz (drawn (G.CapeT s) x) u).trans (card_le_card (show glitches T γ x.1 ⊆ misses x.1 γ from filter_subset ..)))
 have hv:= frost_nn Λ.K.top.clip xₛ ((zero_le_one.trans Y.oneP).trans (Vale.crown ..))
 apply (Marks.read_within F x _).trans; refine (mul_le_mul (V.cost p (drawn (G.CapeT s) x)) (pX.budget x) (norm_nonneg _) (pow_nonneg he _)).trans ?_
 rw [mul_pow]; change c^n * Real.exp C ≤ c^n*Real.exp (-λX)^n*Real.exp (C+(V₁:ℝ)*λX); rw [mul_assoc,←Real.exp_nat_mul,←Real.exp_add]; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (by linarith only [mul_le_mul_of_nonneg_right hs hv])) (pow_nonneg he _)

lemma chosen_M {b:Family (tent Y h)}{S:Finset Cover}(t:InTest (tent Y h) true S false b) (w:0≤c) (C:0≤r)
 (p:∀ᶠ i in atTop, (∀ x:Fields (side Y (u i) s), ‖(sold Y h s (u i) b) x‖ ≤ c) ∧ Glints 1 (region S (side Y (u i) s)) (Pressure.temp (hat Λ.R.L Λ.x s)) (sold Y h s (u i) b))(d:ℕ)(gd:∀ i:Axis,∃ p:ℤ,∀ x∈ S,p ≤ x i∧ x i≤p+d):
    ‖E s b‖ ≤ c * Real.exp (-(frost Λ.K.top.clip (hat Λ.R.L Λ.x s))) * Real.exp (slopeF Λ.W r * ((4:ℝ)*(d+addgap (tent Y h):ℕ))^4) := final_score Y h X s t (mul_nonneg w (Real.exp_pos _).le) (p.mono fun i p=> GlossBill X P w p.1 p.2) P d gd C
end Quest
end YM.CF.Buffered.Afterglow.Hierarchy
