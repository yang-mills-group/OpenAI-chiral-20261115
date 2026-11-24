import Lucent.Sub
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation.Yoke.Lucent
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Buffered Buffered.Lifted Skye MeasureTheory NormedSpace
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
open Ballad EmberWind Window Lamour.Bridge Celeste
open WakeInvestment

open Peaks Scree
open Pannier.Chancel Py.Rate.Pannier
open Cube Laic Buffered.Afterglow Journey Dial
open Rous Pressure Worth
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
variable (s i k:ℕ)
set_option quotPrecheck false
local notation "■" => RootBook Y i k s
local notation "ℕ'" => side Y i s
local notation "flatP" => Dial.spar P.K.j (RootBook Y i k s).J.M (1:Pane (side Y i s))
open Buffered.Afterglow
open Window Cliplet

open Buffered.Afterglow.Tower
open Gist Kea Onyx Papal
open Vale Jewel
variable {I:Type}[Fintype I]
local notation "X" s:max => hat P.R.L P.x s
local notation "λₐ" s:max t:max => sPow P s t
local notation "ψ" s:max => chip (hat P.R.L P.x s) (-3)

open Buffered.Afterglow.Tower
variable {ζι ζη π μ:ℕ→ℕ} {H:Real.exp 1≤P.x}
variable {Φ0:ℕ→ Buffered.Family (tent Y H)→ℕ→ℂ}{E:ℕ→ Buffered.Family (tent Y H)→ℂ}
variable {D:ℕ→ Buffered.Family (tent Y H)→Buffered.Family (tent Y H)}
variable (U:Universal Y H ζι ζη Φ0 E) (Q:Coherent (i:=ζι) (k:=ζη) (E:=E) Y H D π μ)
local notation "iA" => ζι ∘ π
local notation "kA" => ζη ∘ μ
variable (m a:ℕ){M A C:ℝ}(R:ℕ→ℝ)(r:ℕ→ℕ)
variable (β:ℕ→ℝ)(S:Stencil I)(W:ℕ→I→Staff)(b:ℕ→ℕ)
local notation "N" s:max j:max => side Y ((ζι ∘ π) j) s
local notation "G₀" s:max => κFix β s
open Ember (pinch pinch_pos)
def diet (s:ℕ):ℝ:= (2:ℝ)⁻¹^s
lemma diet_p (s:ℕ):0 < diet s:=by unfold diet; positivity
lemma diet_zero:Tendsto diet atTop (𝓝 0):=tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

local notation "ζ" s:max j:max => maxZoom (R s) m a * signature Y s ((ζι ∘ π) j) ((ζη ∘ μ) j) (W s) (κFix β s) S (b s)
local notation "Tiff" s:max => (E s (rider P β (tent Y H) (W s) (b s) S s (R s) m a))
local notation "Book" s:max j:max => MixedBox Y s ((ζι ∘ π) j) ((ζη ∘ μ) j) M C A I m a
local notation "ℓexp" s:max => Expense P s A S (W s) (b s)
structure Swim (M C A:ℝ)(s j:ℕ):Prop where
 pad: Kea.Pad P.K.j (N s j)
 skinny : (r s:ℝ)*pinch (N s j) ≤ diet s
 narrow : R s*pinch (More (N s j))≤ diet s
 wick: dist (reachCost Y s (iA j) (kA j) (κFix β s)) 1 ≤ diet s
 sharp: Expense P s A S (W s) (b s) → dist (ζ s j) (Tiff s) ≤ diet s
 book: (∀ᶠ k in atTop,MixedBox Y s ((ζι ∘ π) k) ((ζη ∘ μ) k) M C A I m a) → MixedBox Y s ((ζι ∘ π) j) ((ζη ∘ μ) j) M C A I m a
#check @Gathering
#check @paidFix

lemma pinching {ns:ℕ→Side}{v:ℝ} (h:Tendsto (fun i=>(ns i).val) atTop atTop): Tendsto (fun i=> v*pinch (ns i)) atTop (𝓝 0):= by
 simpa [Function.comp_def,Ember.pinch,div_eq_mul_inv,mul_assoc] using ((tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R:=ℝ)|>.comp h)).const_mul (v*Real.pi))

local notation "sail!" s:max j:max => Swim (ζι:=ζι) (π:=π) (ζη:=ζη) (μ:=μ) (E:=E) Y m a R r β S W b M C A s j

include U Q
lemma sways (M C A:ℝ) {f:ℕ→ℕ} (g:Pooling Y iA kA f β)(s:ℕ) : ∃ j,Swim (ζι:=ζι) (π:=π) (ζη:=ζη) (μ:=μ) (E:=E) Y m a R r β S W b M C A s j:=by
 have hw:=U.pick.grow_i.comp Q.growsA
 have hn:Tendsto (fun i:ℕ=>(N s i).val) atTop atTop:=by
    have hy:= (Papal.count_la Y s).comp hw.tendsto_atTop
    apply Filter.tendsto_atTop.mpr; intro a; filter_upwards [(Filter.tendsto_atTop.mp hy) ⟨a+1, Nat.zero_lt_succ _⟩] with i h
    change a+1≤(N s i).val at h; omega
 have hN:Tendsto (fun i:ℕ=>(More (N s i)).val) atTop atTop:=tendsto_atTop_mono (fun i=>show (N s i).val ≤ _ from by change _ ≤ (N s i).val *2; omega) hn
 have t:= diet_p s

 let G(j):=MixedBox Y s ((ζι ∘ π) j) ((ζη ∘ μ) j) M C A I m a
 have h:∀ᶠ j in atTop, Expense P s A S (W s) (b s) → dist (ζ s j) (Tiff s) ≤ diet s:= by
    by_cases p:Expense P s A S (W s) (b s)
    · refine (Metric.tendsto_nhds.mp (sharpScale (m:=m) (a:=a) (R:=R s) (β:=β) Y U Q s p) _ t).mono fun j e _=>e.le
    exact Eventually.of_forall fun _ x=>(p x).elim
 have l:∀ᶠ j in atTop,(∀ᶠ k in atTop,G k) → G j:=by
    by_cases p:∀ᶠ k in atTop,G k; exact p.mono fun _ h _=>h; exact Eventually.of_forall fun _ x=>(p x).elim
 obtain ⟨j,v,p,c,d,w,z⟩:= ((Metric.tendsto_nhds.mp (Gathering Y g s) _ t).and
      (g.up.tendsto_atTop.eventually ((hw.tendsto_atTop.eventually (bone_pose Y (nontrivial_spin P) s)).and
       (((pinching (v:=r s) hn).eventually (ge_mem_nhds t)).and
       (((pinching (v:=R s) hN).eventually (ge_mem_nhds t)).and (h.and l)))))).exists
 exact ⟨f j,p.1,c,d,v.le,w,z⟩

omit U Q
lemma Crossing {j:ℕ→ℕ} (v:Velocity P R r)
    (g:∀ s, Swim (ζι:=ζι) (π:=π) (ζη:=ζη) (μ:=μ) (E:=E) Y m a R r β S W b M C A s (j s)):
    ToWick Y id (iA ∘ j) (kA ∘ j) (κFix β) R r:=by
 refine ⟨⟨v.t, v.matter, squeeze_zero (fun s=> mul_nonneg (v.t s).le (pinch_pos _).le) (fun s=> (g s).skinny) diet_zero,fun s=>(g s).pad.1⟩,
         ⟨v.p,v.gauge,squeeze_zero (fun s=>mul_nonneg (v.p s).le (pinch_pos _).le) (fun s=>(g s).narrow) diet_zero,fun s=>⟨(N s (j s)).val,by change (N s (j s)).val * 2= _; omega⟩⟩,v.coupled,fun s=>(g s).pad,?_⟩
 apply Metric.tendsto_nhds.mpr; intro e p; filter_upwards [diet_zero.eventually (gt_mem_nhds p)] with i h; exact (g i).wick.trans_lt h

include U Q
lemma coupon (h:Velocity P R r)
    (e:S.degree m a)(x:∀ᶠ s in atTop,ℓexp s) {d:FieldPlan I}(k:Dusty d S)(u:OnScale d W R r)
    {f}(w:Pooling Y iA kA f β)
    (t:∀ᶠ s in atTop, ∀ᶠ j in atTop, Book s j) (p:dues S ≤ C)(c:candied S M m a ≤ C):
    Tendsto (fun s=> Tiff s) atTop (𝓝 (faq d S)):= by
 choose j g using sways Y U Q m a R r β S W b M C A w
 let F(s):= Tiff s; let Z(s):= maxZoom (R s) m a; let G(s):=dontStop Y s ((ζι∘π) (j s)) ((ζη∘μ) (j s)) (W s) (κFix β s) S
 have ht:Tendsto (fun s=>Z s * G s) atTop (𝓝 (faq d S)):=answered Y (Crossing Y m a R r β S W b h g) u m a S e k
 rw [_root_.tendsto_iff_norm_sub_tendsto_zero] at ht ⊢

 have hz:= (diet_zero.add (h.small m a)).add ht
 rw [zero_add,zero_add] at hz
 refine squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) ?_ hz
 filter_upwards [x,t] with s u v
 let n:= (ζι ∘ π) (j s)
 obtain ⟨y,ℓ,l,r',h',t'⟩:=u
 have hv: AtClinic Y s n M C A I S m a (W s) (κFix β s) (b s):= by
   obtain ⟨o,h⟩:=r' (side Y n s)
   exact ⟨e,y,p,c,⟨ℓ,l,o,h,t',h'⟩,paidFix Y w H _⟩
 let J:=signature Y s n ((ζη∘μ) (j s)) (W s) (κFix β s) S (b s)
 have h:= (g s).sharp ⟨y,ℓ,l,r',h',t'⟩
 rw [dist_comm,dist_eq_norm] at h
 apply (norm_sub_le_norm_sub_add_norm_sub (F s) (Z s*G s) _).trans
 gcongr
 apply (norm_sub_le_norm_sub_add_norm_sub (F s) (Z s*J) _).trans
 rw [←mul_sub (Z s), norm_mul]
 exact add_le_add h (mul_le_mul_of_nonneg_left ((g s).book v _ _ _ _ hv) (norm_nonneg _))
#print axioms coupon
