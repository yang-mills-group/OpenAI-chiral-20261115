import YM.SU5.May.FloePrice
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 30000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.May.Floe
open Function Filter Finset Fir Lattice Laurent Next.Free Bloch Lat Ember Jill Rush
open scoped Topology BigOperators ContDiff InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open Onyx Fock SU Flare Kea Sods Emu Dial Cube Tulip Spire Scroll Thera
open Fock Reflect
open Lamour (lakeP lakeK)
open Hygrometry Personality PriceCliff
open RG Wilson Phase Mir Vale Vale.Grace Peaks Paige Vault
open Stationary (Gaia)
open Buffered.Lifted Buffered.Afterglow.Tower.Tilted
open scoped ComplexOrder
local notation "Ω" => Complex.I
variable {K: Pressure.Teller group} {P: Patch}{B:Side}{e:ℝ}{Y: Pricing K.j P.L P.odd_side (Thread K.j)}(A:Grasp Y B e)(g:0≤e)(h:1≤K.j) (p:Pearl A) (u:Stamped K.j P.L P.odd_side Y)
variable (R:Ramp)(X X':Finset Personality) (κ:ℕ)
variable {n:ℕ→Side} {S:ℕ→Side}(G:∀ i:ℕ, Ratio (CSide (n i) B) (CSide (S i) B))(Q:Twilight K.j G)
local notation "Tᵢ" i:max=> CSide (n i) B
local notation "M" i:max=> hail _ (Q.coordinates i)
local notation "N↑" i:max=> Ratio.count (G i)
local notation "Ta"=> whisper R
local notation "Tb" y:max=> (whisper R).cell y
local notation "Π" i:max=> SpinPrice (changeM A (1:Skye.Pane (CSide (n i) B)) (M i))
universe o o'
variable {rr:ℝ} (e':0<rr)
noncomputable def Fulfills (e':ℝ) (i:ℕ) : Prop:= ∀ (α:Type o)[LinearOrder α][Fintype α](β:Type o')[Fintype β] (U:α→ Cover)(Z:α→Personality) (w:∀ t,Z t∈ X)(a:∀ j,Clear R K.j (U j))(Qp:∀ s t, Smallish (Cube.CSide (n i) B) ((whisper R).cell (U s)-U t)) (F:β→ List α)(e:∀ t,(F t).length≤κ)(v:β→ℂ)(b:Bool)(y:∀ i,wheat (F i)=b), -(e'*(∑ i,‖v i‖)^2) ≤ (SpinPrice (changeM A (1:Skye.Pane (CSide (n i) B)) (hail _ (Q.coordinates i))) (poseX (whisper R) b (utter U Z (CSide (n i) B) 1 F v))).re
include A g h p u
private lemma esteem {m:Side}{N:Jill.Male}{D d:ℝ} {S : ℕ → Side}{rr:ℕ→ℝ}(W:Pad K.j (Cube.CSide m B))(d':0≤d)(t:A.roundZ ≤ (CSide m B).val)(z:Yard (fun i=> CSide (S i) B) rr)(q:BudgetPoint) {α:Type o}[LinearOrder α][Fintype α]{β:Type o'}[Fintype β](U:α → Cover)(Z:α→Personality)(w:∀ j,Clear R K.j (U j))(f:1≤D)(F:β→List α)(L:∀ i,(F i).length≤κ)(v:β→ℂ)(b:Bool)(y:∀ i,wheat (F i)=b) (P:∀ i j:α⊕α,‖reality R N U Z (Cube.CSide m B) K.j i j‖≤D)(H:∀ i j:α⊕α,‖reality R N U Z (Cube.CSide m B) K.j i j-myth R N U Z (Cube.CSide m B) K.j i j‖≤d) : -(rimeCost κ (D+d) * d*(∑ i,‖v i‖)^2) ≤ (SpinPrice (changeM A (1:Skye.Pane (CSide m B)) N) (poseX (whisper R) b (utter U Z (CSide m B) 1 F v))).re:=by
 let a:=reality R N U Z (Cube.CSide m B) K.j; let c:=myth R N U Z (Cube.CSide m B) K.j
 rw [startingPose A g h R N t W U Z b F v y]; have hf:= quota_lens Z F v a c d (D+d) (f.trans (le_add_of_nonneg_right d')) d' (fun i j=>(P i j).trans (le_add_of_nonneg_right d')) (fun i j=> (norm_le_norm_add_norm_sub' _ _).trans (add_le_add (P i j) ((norm_sub_rev (c i j) _).le.trans (H i j)))) H κ L; -- tune $ε Z'
 have hk:= (Complex.le_def.mp (payment_promise A g h p u R N t W U Z F v _ z q w)).1; let W(x):ℂ:=∑ i,∑ j,star (v i)* Arctic.thaw (tariff∘Z) x (F i) (F j)*v j
 have hl: -rimeCost κ (D+d) * d*(∑ i,‖v i‖)^2 ≤ (W a-W c).re:=by have he:=abs_le.mp ((Complex.abs_re_le_norm (W a-W c)).trans hf); rw [neg_mul,neg_mul]; exact he.1
 rw [Complex.sub_re] at hl; change 0 ≤ (W c).re at hk; change _ ≤ (W a).re; linarith only [hl,hk]
include Q
lemma epoch_grant (q:BudgetPoint)(ε:ℝ)(ε':0<ε): ∀ᶠ i in atTop, Fulfills.{o,o'} A R X κ G Q ε i := by
 let X':=X ∪ X.image (whisper R).role
 obtain ⟨C,t,H⟩:= Hearth.reimburse h
 let V0:= ∑ i∈X', Hearth.lump i; let D:=1+C*V0*V0
 have hv:∀ i:Personality,Hearth.lump i ≥0:= Hearth.lump_nonneg; have ht: 0≤V0:=sum_nonneg fun i _=>hv i; have he:1≤D:=le_add_of_nonneg_right (by positivity)
 have hy:∀ i∈X',Hearth.lump i ≤ V0:=fun i k=>single_le_sum (f:=Hearth.lump) (fun i _=>hv i) k
 have hη:Tendsto (fun d:ℝ=> rimeCost κ (D+d)*d) (𝓝[>] 0) (𝓝 0):=by simpa only [add_zero,mul_zero] using ((show Continuous fun d=>rimeCost κ (D+d)*d from (by unfold rimeCost; fun_prop)).continuousWithinAt (s:=Set.Ioi (0:ℝ)) (x:=0)).tendsto
 obtain ⟨d,hD,d'⟩:= ((hη.eventually (ge_mem_nhds ε')).and (self_mem_nhdsWithin (α:=ℝ) (s:=Set.Ioi 0) (a:=0))).exists
 change 0<d at d'; obtain ⟨k,v⟩:=gave K.j h
 filter_upwards [Q.cpu.eventually_ge_atTop k,Q.cpu.eventually_ge_atTop A.roundZ,(X'.eventually_all).2 fun x _=>(X'.eventually_all).2 fun y _ => receipt x y G h d' Q R] with i k z u'
 rintro α c hℓ β Zℓ U Z b p' a F hB w Bη t_w
 refine le_trans (a:=_) (b:= -(rimeCost κ (D+d)*d*(∑ i, ‖w i‖)^2)) (neg_le_neg ?_) (esteem A g h p u R κ (v _ (Q.orientation i) k) d'.le z Q.yards q U Z p' he F hB w Bη t_w ?_ ?_) -- Pad arg placeholder choose.e
 · exact mul_le_mul_of_nonneg_right hD (sq_nonneg _)
 · intro x y; let L:= Packed (whisper R) Z; have hx(k: α⊕α): L k∈X':= by rcases k with x|x; exact mem_union_right _ (mem_image_of_mem _ (b x)); exact mem_union_left _ (b x)
   exact (H _ (Q.orientation i) (M i) (posted (whisper R) U x) (posted (whisper R) U y) (L x) (L y)).trans ((mul_le_mul (mul_le_mul_of_nonneg_left (hy _ (hx x)) t.le) (hy _ (hx y)) (hv _) (mul_nonneg t.le ht)).trans (le_add_of_nonneg_left zero_le_one))
 rintro (x|x) (y|y)
 · change ‖_ - reality R _ _ _ _ _ _ _‖≤ d; rw [sub_self,norm_zero]; exact d'.le
 · exact u' _ (mem_union_right _ (mem_image_of_mem _ (b x))) _ (mem_union_left _ (b y)) _ _ (a x y) (always_gap R (U x) (U y) (p' x) (p' y))
 all_goals simp only [myth,sub_self,norm_zero,d'.le]
end YM.CF.May.Floe
#print axioms YM.CF.May.Floe.epoch_grant
