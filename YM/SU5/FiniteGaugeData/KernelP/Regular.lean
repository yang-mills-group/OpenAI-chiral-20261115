import YM.SU5.FiniteGaugeData.KernelP.Assay
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
set_option quotPrecheck false
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)
local notation "Kₜ"=> tent Y h
local notation "N₁" i:max s:max=> side Y i s
local notation "Wₐ" i:max s:max => (Y.voyage i).CapeT s
local notation "D₀"=> aliasLaw Λ
local notation "D₁"=> distanceLaw l
local notation "L₁"=> Λ.R.L
local notation "C₀"=> (VolumeCape.Dream.plot l).C
local notation "Xᵣ" i:max k:max=> (Y.voyage i).X (Y.uv k)
local notation "Tᵣ" i:max k:max s:max=> ((Y.voyage i).X (Y.uv k)).gram s
variable (S T: Finset Cover)(s i k:ℕ)
open Nacre Heat Charm Chrono SalonG Journey Hills Playlist Show
namespace KernelP
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}{P:Call Λ l}{J:Wicket Λ l}
variable (W':Universal Y h u v I E)(R:Rolled Y h u v J P)(A:∀ a:Axis,Repertory Y h W' R a)
variable {Φ:ℕ→ Charm.W (tent Y h)→ₗ[ℂ]ℂ}(S':Sphere Y h W' R A Φ)
variable (a:Axis)(z:ℤ)(d n:ℕ)
open scoped NNReal ENNReal
local notation "D"=> Decko Y h a
variable (H:Harbor Y h W' R Φ a)(X:Engine Y h W' R a H)(j:Axis)
local notation "M" s:max=> H.leaf s
local notation "F"=> H.space
local notation "T"=> X.val
local notation "Q" s:max=> X.val.onceL s a
private lemma kinesis {H:Hilbert}{L:Side}(V: Terrace H L a)(s:ℕ): V.onceL 0 a=(V.onceL s a)^(L.val^s):=by
 induction s with
 | zero=> rw [pow_zero,pow_one]
 | succ s ih=>
    have hx: V.onceL s a= V.stepT (s+1) a (L.val:ℤ) (fun _=>Nat.cast_nonneg' _):= (V.repeats s a 1 _ (fun _=>by positivity)).trans (by congr 1; rw [mul_one]); rw [ih,hx,V.atom_pows,← pow_mul,pow_succ' L.val]
include X S'
lemma mobile (p:Allows a j z)(v:j≠a)(y:F): ‖X.val.stepT s j z p y‖ = ‖y‖:=by
 let M' := X.val.stepT s j z p; let Z:=X.val.stepT s j (-z) (fun h=> (v h).elim)
 have he: Z (M' y)=y:= by rw [← mul_apply_eq_comp]; have t: Z*M'=1:= (X.val.via s j (-z) z 0 (fun t=>(v t).elim) p _ (neg_add_cancel z)).trans ((T).ident ..); rw [t]; rfl -- binder via _ tuning
 have hp(U:H.space.Op)(v:‖U‖≤1)(x:F):‖U x‖ ≤ ‖x‖:= (U.le_of_opNorm_le v _).trans_eq (one_mul _)
 exact le_antisymm (hp M' ((T).size_ ..) _) ((congrArg (norm : F→ℝ) he).symm.le.trans (hp Z ((T).size_ ..) (M' y))) -- eq_subst nuance
lemma votive (k:ℕ): 0 ≤ (T).stepT s a k (fun _=>Nat.cast_nonneg' _):= by
 let P:= (T).stepT s a k (fun _=>Nat.cast_nonneg' _); apply (ContinuousLinearMap.nonneg_iff_isPositive _).2; apply paidpositive; intro y; apply leaf_lift Y h s W' R a H {x | 0 ≤ inner ℂ x (P x)} (isClosed_le continuous_const (continuous_id.inner P.continuous)) _ y
 intro i hS x; change 0 ≤ inner ℂ _ (P _); unfold P; rw [Vessel Y h s i W' R a (k:ℤ) a H X x _ hS,H.measure]; apply timePos S' i _ x _ (mul_nonneg (by positivity) (Nat.cast_nonneg' k)); positivity
where
 timePos {A':∀ a:Axis,Repertory Y h W' R a}(p:Sphere Y h W' R A' Φ)(t:ℕ)(z:ℤ)(x:D)(e:0≤z)(v:0≤z) : 0 ≤ Φ t (helve Kₜ a x.val (hoist Y h a a z (fun _=>e) x).val):=by obtain ⟨n,rfl⟩:= Int.eq_ofNat_of_zero_le v; exact (p.hardy t a x n).1 -- duplicate e
lemma wand_nn : 0≤ Q s:=votive Y h s W' R A S' a H X 1

-- account for all real t. unit tick^Λ.L.
def regular (t:ℝ≥0):= anise t ((X.val).onceL 0 a)
#check regular
lemma atemporal (k:ℕ): regular Y h W' R a H X (thetaX Λ s k)=X.val.stepT s a k (fun _=>Nat.cast_nonneg' _):= by rw [regular,kinesis a X.val s,X.val.atom_pows]; exact anise_table (Q s) (wand_nn Y h s W' R A S' a H X) (tassel Λ s) k (show 0<tassel Λ s from tassel_pos s) -- k
local notation "A'"=> regular Y h W' R a H X
@[simp] lemma regular_zero : regular Y h W' R a H X 0=1:= anise_zero (Q 0) (wand_nn Y h 0 W' R A S' a H X)
lemma regular_time (t u:ℝ≥0): regular Y h W' R a H X (t+u)= A' t * A' u:=power_sum (Q 0) (wand_nn Y h 0 W' R A S' a H X) t u
omit S' in
lemma regular_nn (u:ℝ≥0): 0 ≤ regular Y h W' R a H X u:=anise_nn ..
lemma regular_bounds (u:ℝ≥0): ‖regular Y h W' R a H X u‖≤ 1:=anise_norm (Q 0) (wand_nn Y h 0 W' R A S' a H X) ((T).size_ ..) u
omit S' in
lemma regular_coin (t:ℝ≥0)(z:ℤ)(p:Allows a j z): Commute (regular Y h W' R a H X t) (X.val.stepT s j z p):= anise_free (Q 0) t ((T).stepT s j z p) ((T).cool ..) -- .cool proof
-- continuity prerep.Warm.Band growing through Epoch.EXTRA.
private lemma prepaid (x:D):∃ y:H.space, (X.val.stepT (s+tic Kₜ) a 1 (fun _=>zero_le_one)) y= (M s) x:= by
 have he(n:ℕ):∃ y:D, Canaan Y h a y.val n ∧ (M (s+n)) y=(M s) x:=by
    induction n with
    | zero=>exact ⟨x,by rw [Nat.cast_zero]; exact x.property,rfl⟩
    | succ n ih=> obtain ⟨y,u,b⟩:=ih; exact ⟨nectar Y h (s+n) W' R a y,by rw [Nat.cast_succ]; exact nectar_beyond Y h _ W' R a y (Nat.cast_nonneg' _) u,(H.up Y h (s+n) W' R a y).trans b⟩
 let n:=tic Kₜ; obtain ⟨y,p,q⟩:= he n; let g:=clockW Kₜ a (-1) y.val
 have he:Canaan Y h a g 0:= by have hv:= Canaan.flight Y h a _ (-1) p; change Canaan Y h a g ((n:ℤ)+n*(-1:ℤ)) at hv; rwa [mul_neg,mul_one,add_neg_cancel] at hv
 let v: Decko Y h a:=⟨g,he⟩; exact ⟨(M (s+n)) v,(X.property ..).trans ((congrArg (H.leaf _) (show hoist Y h a a 1 (fun _=>zero_le_one) v=y from Subtype.ext (by rw [hoist_val,show v.val=g from rfl]; unfold g; rw [clock_add,add_neg_cancel,tic_zero]))).trans q)⟩

set_option maxHeartbeats 440000 in
lemma regular_all (v:H.space): Continuous (fun t=> (regular Y h W' R a H X t) v):=by
 -- use warmth for all mixed vectors dense. continuous at positive by embedding CFC; through zero true if warmed by t.
 have he (i:ℕ) (x:Decko Y h a): Continuous (fun t=> (regular Y h W' R a H X t) ((H.leaf i) x)):=by
    obtain ⟨y,q⟩:= prepaid Y h i W' R A S' a H X x; let t:=thetaX Λ (i+tic Kₜ) 1; have hv:0<t:=div_pos (by exact_mod_cast zero_lt_one) (Nat.cast_pos.mpr (tassel_pos _)); have hy:(A') t y=(M i) x:=(congrArg (fun f:H.space.Op=> f y) (atemporal Y h (i+tic Kₜ) W' R A S' a H X 1)).trans q -- defeq Nat.cast_one
    let Q1(u:ℝ≥0):= regular Y h W' R a H X (u+t); have hQ:Continuous Q1:= (power_op_pos (Q 0) (wand_nn Y h 0 W' R A S' a H X)).comp_continuous (continuous_id.add continuous_const) (fun i=> show 0 < i+t by positivity)
    suffices e: (fun u=> ((A') u) ((M i) x)) = fun u=> Q1 u y by rw [e]; exact (ContinuousLinearMap.apply ℂ H.space.space y).continuous.comp hQ
    exact funext fun u=> by rw [← hy]; unfold Q1; rw [regular_time Y h W' R A S' a H X]; rfl
 have hx (w:Vect Y h a 0): Continuous fun t=> regular Y h W' R a H X t (H.value w):=by obtain ⟨n,t⟩:= (PortWhole Y h W' R a H w).exists; dsimp only at t; rw [←t]; exact he n _
 refine continuous_iff_continuousAt.mpr fun x=> Metric.tendsto_nhds.mpr fun ε hε=>?_
 obtain ⟨g,⟨k,rfl⟩,z⟩:= Metric.mem_closure_iff.mp (H.varied v) (ε/4) (by positivity); have hw(y:ℝ≥0): dist (((A') y) v) (((A') y) (H.value k)) < ε/4:=by rw [dist_eq_norm,←map_sub]; exact lt_of_le_of_lt ((((A') y).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (regular_bounds Y h W' R A S' a H X y))) (by simpa [dist_eq_norm] using z)
 filter_upwards [Metric.tendsto_nhds.mp ((hx k).continuousAt (x:=x)).tendsto (ε/4) (by positivity)] with y v0
 have z':= dist_triangle (((A') y) v) (((A') x) (H.value k)) (((A') x) v); have hu:= hw x; rw [dist_comm] at hu; have ht:= dist_triangle (((A') y) v) (((A') y) (H.value k)) (((A') x) (H.value k)); linarith [hw y]
#print axioms regular_all
end KernelP
end YM.CF.Buffered.Afterglow.Hierarchy
