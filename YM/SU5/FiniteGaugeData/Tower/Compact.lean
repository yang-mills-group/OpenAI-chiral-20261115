import YM.SU5.FiniteGaugeData.Tower.Palette
/-!
# Simultaneous subsequence, full uniform on each field

Use countable sets probing uniform menus (asked on each fixed field) and the
input fleet. Works even when the underlying values at each stage are just
Borel, so no AA extension to continuous functions. This is the reaching
compactness we'd need to preserve products of transferred arguments, stronger
than weak-star (Banach-Alaoglu on field by field readings) and asks for the
Menu estimates on this varying block (not on the reading functionals alone).
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Satin
open scoped Topology Classical

variable {I:Type*}[Countable I]{T X:I→Type*}[∀i,MeasurableSpace (X i)](S:(i:I)→Set (T i))(F:(i:I)→ ℕ→ T i→ X i→ℂ)
structure Orchestra : Prop where
 decks (i:I)(a:T i): Menu (T:=fun _=>ℂ) (fun (n:ℕ) x=> F i n a x)
 admits (i:I)(ε:ℝ): 0<ε→∃ a:Finset (T i), ∀ᶠ n₀ in atTop, ∀ m∈S i,∃ v∈a, ∀ n≥n₀, ∀ y, dist (F i n m y) (F i n v y) ≤ε

lemma simultaneous_cauchy (h:Orchestra S F):∃ f:ℕ→ℕ,StrictMono f∧∀(i:I)(ε:ℝ),0< ε→ ∀ᶠ n₀:ℕ in atTop,
    ∀ n≥n₀,∀ m≥n₀, ∀ a∈S i,∀ b:X i,dist (F i (f n) a b) (F i (f m) a b)<ε:=by
 let r(n:ℕ):ℝ:=(1/2:ℝ)^n; have hr(n):0<r n:=by positivity
 choose p q using fun (i:I)(n:ℕ)=> h.admits i (r n) (hr n)
 let J:=Σ i:I,(Σ n:ℕ,↥(p i n))
 let A(j:J):ℕ→X j.1→ℂ:=fun n=> F j.1 n j.2.2.val
 have a(j:J): Menu (A j):=h.decks j.1 j.2.2.val
 choose d D W using fun (j:J)(n:ℕ)=> (a j).deal _ (hr n)
 choose K hk H using fun (j:J)=> (a j).budget
 let l(j:J)(n:ℕ): Set (d j n).Sign:= Set.range (d j n).idT
 choose σ hσ using fun (j:J)(n:ℕ)(i: ↑(l j n))=> i.property -- fails property range reducible?
 let B:=Σ j:J, (Σ n:ℕ, ↥(l j n))
 let aK(j:B):= Metric.closedBall (0:ℂ) (K j.1)
 let k(n:ℕ)(j:B):aK j:=⟨A j.1 n (σ j.1 j.2.1 j.2.2), mem_closedBall_zero_iff.mpr (H _ _ _)⟩
 haveI(j:B):CompactSpace (↥(aK j)):= isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
 -- need Countable sigma nested
 obtain ⟨Z,f,h,hF⟩:= CompactSpace.tendsto_subseq k
 refine ⟨f,h,fun i ε ε'=>?_⟩
 obtain ⟨R,hR⟩:= ((show Tendsto r atTop (𝓝 0) from tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).eventually (gt_mem_nhds (by linarith:0<ε/5))).exists
 obtain ⟨n₀,hn⟩:= (q i R).exists; let t:=r R
 have hv(j:B):CauchySeq (fun n=>A j.1 (f n) (σ j.1 j.2.1 j.2.2)):= Filter.Tendsto.cauchySeq ((continuous_subtype_val.tendsto (Z j)).comp (tendsto_pi_nhds.mp hF j)) -- cauchySeq name search
 let L:= ↥(p i R); let N(a:L):J:=⟨i,R,a⟩
 let b(a:L)(u:↥(l (N a) R)):B:=⟨N a,R,u⟩
 have hm :∀ᶠ n:ℕ in atTop,∀ (x:L)(u:↥(l (N x) R)),∀ j≥n,∀ k≥n,dist (A (N x) (f j) (σ (N x) R u)) (A (N x) (f k) (σ (N x) R u)) < t:=by
    rw [eventually_all]; intro x; rw [eventually_all]; intro u
    obtain ⟨R₁,m⟩:= Metric.cauchySeq_iff.mp (hv (b x u)) t (hr R)
    exact (eventually_ge_atTop R₁).mono fun w z j v k h=> m j (z.trans v) k (z.trans h)
 filter_upwards [h.tendsto_atTop.eventually_ge_atTop n₀,hm] with n E v j g k w m pH x
 obtain ⟨z,zH,q⟩:= hn m pH
 have P:= q (f j) (E.trans (h.monotone g)) x; have Q:= q (f k) (E.trans (h.monotone w)) x
 let u:L:=⟨z,zH⟩; let σx:↥(l (N u) R):=⟨(d (N u) R).idT x,Set.mem_range_self x⟩; let y:=σ (N u) R σx
 have hxy:(d (N u) R).withZ x y:= (d (N u) R).id_spec _ _ (hσ (N u) R σx).symm
 have Y(a:ℕ):dist (F i (f a) z x) (F i (f a) z y)< t:=W (N u) R x y hxy _
 have H:dist (F i (f j) z y) (F i (f k) z y)< t:= v u σx j g k w
 let A₁:=F i (f j); let A₂:=F i (f k)
 have π: dist (A₁ m x) (A₂ m x) < 5*t:=by
    calc
     dist (A₁ m x) (A₂ m x) ≤ dist (A₁ m x) (A₁ z x)+dist (A₁ z x) (A₂ m x):=dist_triangle ..
     _ < 5*t:=by
       have h₁:=dist_triangle (A₁ z x) (A₁ z y) (A₂ m x)
       have h₂:=dist_triangle (A₁ z y) (A₂ z y) (A₂ m x)
       have h₃:=dist_triangle_right (A₂ z y) (A₂ m x) (A₂ z x)
       rw [dist_comm (A₂ z y) (A₂ z x)] at h₃
       unfold A₁ A₂ t at *; linarith [Y j,Y k]
 exact π.trans_le (by unfold t; linarith)

end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.simultaneous_cauchy
