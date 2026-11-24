import Gingham.Ruff.Music
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 4000
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Gingham.Ruff
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset RG Cube
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical
open Skye Scree
local notation "γ"=>SU.group
open Jet Rill Sour Lat Tulip
variable {N:Side}


open Drapes Fock Peaks Branch Tenant
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra

open Forge Vow
variable {n:ℕ}{a c e ρ b:ℝ} (X:Rialto n e ρ b)
    {A:Fob N e}
   {y:Site N}{u:Side}
variable (B:Plastron y u e (a/4) c A)
variable {l r:ℕ}{E:ℝ}{p: BudgetPoint}
  (G:Tagbill a E u l r p.B)
  (P: Parasols p ρ (p.B/10))
variable {Z:Scree.Loom N} (F:Briefly p r e Z)
include G F

lemma fully(x:Orbit N)(v: pingS p.threshold (hoop y p.B) x.1):
 Agrees (belle y p.B) x.1 (Z x):=by
 have hv:=ping_le (pingWide v F.ceiling.1)
 intro i j k
 refine (F.ceiling.2.lamp x.1 x.2 i
    (hv.symm.mono_right ((Corona.halo_mono le_rfl
       (insert_subset j (singleton_subset_iff.mpr k))).trans ?_))).symm
 exact halo_spread
   (fun z q=>by simpa [belle,hoop, halo_spec] using q)
   (show r+p.B/10≤p.B from by have :=G.largeB;omega)

omit G F
lemma wing_k (p:BudgetPoint)(D:Support (More N)):‖(wakeB (unrest D p.B):tangD N→L[ℝ]tangD N)‖≤1:=by
 apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one;intro i
 rw [one_mul]
 refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j=>?_
 rw [steadyB]; split;exact norm_le_pi_norm ..
 rw [norm_zero];exact norm_nonneg _


private lemma silent_hit (x:Orbit N)(v: pingS p.threshold (hoop y p.B) x.1)
   (D:Support (More N)):
  ∀ᶠ i in 𝓝 0,pingS p.threshold (hoop y p.B) (pressQ p D x.1 i):=by
   refine ((Forge.stickU ..).comp (continuous_id.const_smul p.threshold) |>.tendsto 0).eventually 
      (ping_o.eventually_mem (by simpa [smul_zero,Function.comp_apply,Forge.born] using v))
  -- metavars


include F X G B P
lemma bash (q:2*(p.B/10+1)<(More N).val)(j:2≤n)(h:hum X A 0=0)
   (x:Orbit N)(v: pingS p.threshold (hoop y p.B) x.1)
   (D:Support (More N)):
   Allows n (fun i=> Matrix.trace (coinF F B true (pressQ p D x.1 i,x.2))) 0
      (devour ρ u a c*p.threshold^2 + fairy a p.B*c):=by
  let s:=silent_hit x v D
  obtain ⟨g⟩:=pinwaxes (p:=p) (x:=bouton y) (U:=x.1) _ q
     (Vow.grow_b
      (Corona.halo_mono (show p.B/10+1≤p.B from by have :=G.largeB;omega)
        le_rfl) v)
  let V i:= (pressQ p D x.1 i,x.2)
  have t0:pitch y p x.1 (fun i=>Z (V i)) (wakeB (unrest D p.B)):=by
    refine ⟨wing_k p D,s.mono fun i t=> ?_⟩
    have b: pressQ p D x.1 i=increment x.1 (p.threshold • wakeB (unrest D p.B) i):=by
      unfold pressQ gyrate; rw [←map_smul];rfl


    rw [←b];exact fully G F (V i) t
  apply Allows.germ (chorus X B G P g j h _ (fun i=>F.roll (V i))
     (Eventually.of_forall fun _=>rfl) _ t0)
  exact s.mono fun i z=>congrArg Matrix.trace (by
    simp only [coinF,silkcut,retina,z,if_true];rfl)

lemma basque (q:2*(p.B/10+1)<(More N).val)(j:2≤n)(h:hum X A 0=0)
   (x:Orbit N)(D Z': Support (More N))(Y:Aura N)
   (s:hoop y p.B⊆Y.val)(v:x.1∈σX p Y D):
   Allows n (fun i=> Matrix.trace (coinF F B true (pressQ p Z' x.1 i,x.2))) 0
      (devour ρ u a c*p.threshold^2 + fairy a p.B*c):=by
  by_cases t:pingS p.threshold (hoop y p.B) x.1
  · exact bash X B G P F q j h x t Z'
  refine Allows.germ (allows_const 0 (v:=(0:ℂ)) ?_) ?_ -- reorder
  swap
  · exact (curtain_near p x Z' s v).mono fun i w=>by
      try dsimp
      rw [coinF,silkcut,w,if_neg,Matrix.trace_zero]
      simp [retina,t]


  rw [norm_zero]; have:= Shells.carrot_c B; unfold fairy devour Shells.Interest
  have := Fan.price_nn u (a/4) 2; positivity

#print axioms basque


lemma flashfee (q:2*(p.B/10+1)<(More N).val)(j:2≤n)(h:hum X A 0=0)
   (x:Orbit N): ‖Matrix.trace (coinF F B true x)‖≤
      devour ρ u a c*p.threshold^2 + fairy a p.B*c:=by
  by_cases t:pingS p.threshold (hoop y p.B) x.1
  · have v:= (bash X B G P F q j h x t ∅).value
    simpa only [pressQ,smul_zero,Forge.born] using v
  rw [coinF,silkcut]
  have w:retina p (hoop y p.B) x≠true:=by simp [retina,t]
  rw [if_neg w,Matrix.trace_zero,norm_zero]
  have:=Shells.carrot_c B; unfold fairy devour Shells.Interest
  have := Fan.price_nn u (a/4) 2; positivity


open Pike
omit P in
lemma hearing {w:Doub N}(o:‖w‖<1)
    (x: Orbit N)(v: pingS p.threshold (hoop y p.B) x.1)
    (g:Seat N → SU.E) 
    (d:Agrees (belle y p.B) (pencil ρ w) (gauge g x.1)):
    Matrix.trace (coinF F B true x) = hum X (B.light (tenderb p.B)) w:=by
 let T:=tagLite (b:=p.B) B
 rw [coinF,silkcut,retina,if_pos v,if_pos rfl]
 unfold liteF hum; simp only [comp_apply]
 rw [Shells.aria_kernel X T,Shells.aria_kernel X T]
 apply sum_congr rfl;intro S _
 by_cases h:blush (T.cost S)=0
 · rw [Shells.hush X T S h _,Shells.hush X T S h _]
 obtain ⟨a,t⟩:=Shells.apple_positive T S h
 refine ride X (T.pass S) _ _ g o (Z x) rfl ?_
 have s:S⊆belle y p.B:=girder_i G S a t
 intro i j k
 rw [d i (s j) (s k)]
 unfold Lattice.gauge;rw [fully G F x v i (s j) (s k)]


omit P in
lemma hearsmall (j:3≤n) {w:Doub N}(o:‖w‖<1)
    (x: Orbit N)(v: pingS p.threshold (hoop y p.B) x.1)
    (g:Seat N → SU.E) 
    (d:Agrees (belle y p.B) (pencil ρ w) (gauge g x.1)):
    let f:=hum X (B.light (tenderb p.B))
    ‖Matrix.trace (coinF F B true x)-f 0-quadraticChi f w‖≤c*‖w‖^3:=by
 intro f;rw [hearing X B G F o x v g d];exact Pike.spin X B _ G.apos j o

omit P in
lemma pulse (o:Doub N→ Skye.Ids N):
  (fun v=>Matrix.trace (coinF F B true (pencil ρ v, o v)))
     =ᶠ[𝓝 0] hum X (B.light (tenderb p.B)):=by
  have v: pingS p.threshold (hoop y p.B) (pencil (N:=N) ρ 0):=by
    rw [pencil_flat]
    intro i k
    simpa [faceValue,square, travel] using p.threshold_pos


  have k: Continuous (pencil (N:=N) ρ):=by unfold pencil; fun_prop
  have d:∀ᶠ x:Doub N in 𝓝 0,‖x‖<1:=
     (continuous_norm.tendsto 0).eventually (gt_mem_nhds (by simp))
  filter_upwards [(k.tendsto 0).eventually (ping_o.eventually_mem v),d] with x h t
  exact hearing X B G F t _ h 1 (by intro i _ _; simp [Lattice.gauge])

