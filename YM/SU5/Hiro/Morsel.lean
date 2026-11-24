import YM.SU5.Hiro.Lard
/-! Flat reference moment volatility. Use actual warp (`s × period`) --
 never impose that historic WP side has reached anything about R.
 Credit derivative ∀ cofin i,∀ k. Appliance akin SPF.aroma.
-/
set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Hiro
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Buffered Lifted Bilinear Window Skye Emu Onyx Kea Flare Dial
open Cache Glaze
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
open YM.CF.Lamour YM.CF.Velvet
open YM.CF.Lamour.Bridge.Celeste
open YM.CF.Py.Rate.LocalLimit.Papal (Weaver household)
open Ballad
open Twah (DirSpin)
variable {R:ℕ}{N:Side}{j:ℕ}
section funding
lemma basis_cost (N:Side)(x:Cover)(i:SpinIdx)(b:Slot): ‖basisC N x i b‖=1:=by unfold basisC Lifted.winding; rw [norm_smul,Rush.fee_norm]; simp
lemma roll_c {F:Op (Single N)}{e:ℝ}(p:Billow e F)(x:Cover)(i:SpinIdx)(j:Slot): ‖acts F (basisC N x i j)‖≤e:=by unfold basisC Lifted.winding; rw [map_smul,norm_smul,fee_norm,one_mul]; exact (p _).1
lemma prices_dice (j:ℕ)(p:1≤j)(R:ℕ): ∃ Q>(0:ℝ),∀ {N:Side}, Even N.val → ∀ x y L G (M:Jill.Male), ‖diced R x y L G N j M‖ ≤ Q:=by
 obtain ⟨h,H,Z⟩:= lake_local p; let a:= (R:ℝ)^3*h; let b:= (60:ℝ)*a*a
 have he:0 ≤ a:=by unfold a; positivity
 refine ⟨b+1, by unfold b; positivity,fun {N} hx x y L G M=>?_⟩; let A:= lake N j M; have hv(x y:Cover)(L G:DirSpin): ‖dietary R x y L G N j M‖≤ a:=by
    rw [dietary,in_transcript R x y L G,clear_canvas,hopF]; simp_rw [Ballad.Twah.uncut, norm_mul,norm_pow]; rw [Complex.norm_real,Real.norm_of_nonneg (by positivity : (0:ℝ)≤R)]
    apply mul_le_mul_of_nonneg_left _ (by positivity :0≤ (↑R:ℝ)^3); apply (norm_inner_le_norm ..).trans; rw [basis_cost,one_mul]; exact roll_c (Z hx M) .. -- test implicit ν
 unfold diced; rw [norm_mul,norm_mul,norm_neg]; refine (mul_le_mul ?_ (hv y x G L) (norm_nonneg _) (by positivity : 0≤60*a)).trans (le_add_of_nonneg_right (by norm_num)) ; norm_num; exact hv .. -- tune
end funding
open YM.Stationary (Gaia)
variable {s:ℕ→Side}{r:ℕ→ℕ}{U V:ℕ→ Cover}{M:ℕ→Jill.Male}(L G:DirSpin){X:Gaia}(u:Tendsto (fun i=> riseX (r i) (U i-V i)) atTop (𝓝 X)) (e:X≠0)
variable (W:Yard s (fun i=> (r i:ℝ))) (p:1 ≤ j)
def shotL (x:Gaia) (L G: DirSpin):= pencil x (dnSpin L.2) (upSpin G.1)
include p W u e
lemma roll_shot : Tendsto (fun i=>dietary (r i) (U i) (V i) L G (s i) j (M i)) atTop (𝓝 (shotL X L G)):=by
 simp_rw [dietary,in_transcript]; let i:=sourceSlot; obtain ⟨c,hv,hT⟩:=lake_formal p
 have ht:=Emu.tally (L:=fun i=> (r i:ℝ)) (fun i=>too _) M (fun i=> lakeP _ j (M i)) (fun i=>0) W hv (by norm_num : (0:ℝ)<1) (fun x:Slot=>Eventually.of_forall fun i=>hT _ (W.even i) _ x) (alignedα L i) (alignedβ G i) U V X (Or.inl e) u p (fun _=>1)
 rw [show frank (alignedα L i) (alignedβ G i) X=shotL X L G from if_pos rfl] at ht; exact ht
omit p W u e
def shotR : ℂ:= -60*shotL X L G*shotL (-X) G L -- syntax variable implicit X def check
variable (j)
theorem travel_feast {X:Gaia}(w:1≤j)(r:ℕ→ℕ)(Q:Tendsto r atTop atTop)(W:∀ i,0<r i)(V U:ℕ→ Cover)(u:Tendsto (fun i=> riseX (r i) (U i-V i)) atTop (𝓝 X))(e:X≠0)(a:ℝ)(η:0<a): ∀ᶠ i in atTop,∀ᶠ N:Side in atTop,Even N.val → ∀ M:Jill.Male, dist (diced (r i) (U i) (V i) L G N j M) (shotR L G (X:=X)) ≤ a:=by -- argument order
 by_contra h; obtain ⟨f,t,z⟩:= extraction_of_frequently_atTop (not_eventually.mp h)
 let Qu (i:ℕ):=r (f i); have ht(i:ℕ):0<(Qu i:ℝ):=by unfold Qu; exact_mod_cast W (f i)
 choose Y m v p h using fun i=> (show ∃ (N:Side)(M:Jill.Male), Even N.val∧(Qu i:ℝ)*Ember.pinch N≤ (2:ℝ)⁻¹^i∧ ¬ dist (diced (r (f i)) (U (f i)) (V (f i)) L G N j M) (shotR L G (X:=X))≤ a from by
   obtain ⟨k,v⟩:=Glaze.pick_depth (p:=(show 0<(2:ℝ)⁻¹^i/(Qu i:ℝ) from (by have e:= ht i; positivity)))
   have he:=z i; replace he :=not_eventually.mp he; obtain ⟨N,h,vN⟩:= (he.and_eventually (eventually_ge_atTop (⟨k+1,by omega⟩:Side))).exists; -- remove
   push Not at h; obtain ⟨H,M,g⟩:=h; exact ⟨N,M,H, (mul_comm _ _).le.trans ((le_div_iff₀ (ht i)).1 (v (by change k+1 ≤ N.val at vN; omega))),g.not_ge⟩)
 let Q:= Q.comp t.tendsto_atTop; let d:= u.comp t.tendsto_atTop
 have hx: Yard Y (fun i=> (Qu i:ℝ)):= ⟨ht, tendsto_natCast_atTop_atTop.comp Q,squeeze_zero (fun i=> mul_nonneg (ht i).le (Ember.pinch_pos _).le) p (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)),v⟩
 let A:= U ∘ f; let B:= V ∘ f
 have he:Tendsto (fun i=>diced (r (f i)) (U (f i)) (V (f i)) L G (Y i) j (m i)) atTop (𝓝 (shotR L G (X:=X))):= (((roll_shot (M:=m) (U:=A) (V:=B) L G d e hx w).const_mul (-60)).mul (roll_shot (X:=-X) (U:=B) (V:=A) G L ?_ (neg_ne_zero.mpr e) hx w));
 swap; · exact u.neg.comp t.tendsto_atTop |>.congr fun i=>by rw [show B i-A i= -(U (f i)-V (f i)) by unfold B A; simp]; ext a; simp [comp,riseX,moor]; try ring
 obtain ⟨i,f⟩:= (Metric.tendsto_nhds.mp he a η).exists; exact h _ f.le
end YM.CF.Hiro
#print axioms YM.CF.Hiro.prices_dice
#print axioms YM.CF.Hiro.travel_feast
