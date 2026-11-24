import YM.SU5.Relativistic.Preparing
import YM.SU5.Relativistic.PriceShuffle
/-! # One set of normalizations, periods/cutoffs and preparations for this functional.

No moving the gauge or coupling sequences, still on the same joint cone, and the
preparation is not per stencil. Central observation is written at resolution (as
is updatable boundary at its funding height); see later proof indeed outside the central
observations of any fixed contact-polynomial. -/
set_option autoImplicit false
set_option maxHeartbeats 470000
set_option maxRecDepth 6000
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function NormedSpace Filter Metric Lattice Cube Finset MeasureTheory RG Wilson
open Lat Mir Phase RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Scree Window Vale Girt Lifted
open Py Py.Rate LocalLimit Preparation Satin Heat Fock SlabMark PhaseChoice Push.SectorMeasure
open Tapestry Tapestry.Altitude Tapestry.Exhibition MeshClock
open Tower.Selected Vacancy
open Journey
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
section inGeneral
lemma agenda (P:ℕ→ℕ→Prop)(h:∀ i,∀ᶠ k in atTop,P i k):∃ m:ℕ→ℕ,StrictMono m∧∀i,P i (m i):=by
    choose l t using fun i=> eventually_atTop.mp (h i)
    let g:=fun n=> Nat.rec (motive:=fun _=>ℕ) (l 0) (fun i k=> max (k+1) (l (i+1))) n
    refine ⟨g, strictMono_nat_of_lt_succ (fun i=> lt_of_lt_of_le (Nat.lt_add_one (g i)) (le_max_left ..)), fun i=> t i (g i) ?_⟩
    cases i with| zero=>exact le_refl _ | succ i=> exact le_max_right ..
noncomputable def progressBoard : ℕ → Finset Cover × ℕ := (exists_surjective_nat (Finset Cover × ℕ)).choose
lemma all_boards (K:Calibration)(x:Cloud (Dome K))(p:x∈ FiniteGaugeDataPoly K) : ∃ (k:ℕ) (C:ℝ), Pocket K (fun _=> (progressBoard k).1) (progressBoard k).2 C x:=by
   obtain ⟨n,t⟩:= Altitude.curve.mp p
   obtain ⟨S,e⟩:= anyWords K n _ t
   let M:= (Iic n).biUnion S
   obtain ⟨i,(h:progressBoard _=_)⟩:= (exists_surjective_nat (Finset Cover × ℕ)).choose_spec (M,n) -- tune
   refine ⟨i,?_⟩; rw [h]
   exact issued.mp (coin_mono K S (fun _=> M) n n (fun i p=>subset_biUnion_of_mem S (mem_Iic.mpr p)) le_rfl e)
end inGeneral
section purchase
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
    {L:Rack Λ l}{Θ:Clay Λ l}{T:ℕ→ℕ→ Tariff}{t:ℕ→ Tariff}(D : Fashion Y H i k I E L Θ T t)
local notation "D'"=> D.toExhibition
local notation "V"=> D.univ_
variable (G:SatinVerification.GroundExtension (i:=i) (k:=k) (E:=E) Y H)
variable (j : Axis)(U : ∀ j:Axis,Arena Y H G.history.circuit j 0 false)(q:Panel Y H D.univ_ G.history G.clipped j false (U j))
variable (x:q.X)
local notation "R"=> SameCharacter.resident Y H V G j false (U j) (q.character x)
local notation "M"=> onDrawing Y H V G D' j U R
local notation "γ"=> Dome (tent Y H)
local notation "𝒞"=> Cloud (Dome (tent Y H))
variable (c:∀ i,Future Y H j i)
local notation "ϕ" n:max=> Future.boundary Y H j (c n)

/-- call with extra board payments as needed. does not trade in D. -/
lemma select_rows (extra : ℕ→ℕ→Prop)(e : ∀ b, ∀ᶠ f in atTop,extra b f):
   ∃ m:ℕ→ℕ, StrictMono m ∧ (∀ b,extra b (m b)) ∧
   ∀ b s,s≤b→let r:= i (m b); ∀ A z,Pocket (tent Y H) (fun _=> (progressBoard s).1) (progressBoard s).2 A z → ∀ n:ℕ,
   legacy Y r (k n) → ‖taking Y H r (k n) (z*Future.boundary Y H j (c b)) - vistaTake Y H D.toExhibition (z*Future.boundary Y H j (c b))‖ ≤ propeller b*A:=by
   let bk(n:ℕ):BillOfWork:=fun _=> (progressBoard n).1; let r(n:ℕ):=(progressBoard n).2
   let P(l n w:ℕ):Prop:= ∀ A z, Pocket K (bk n) (r n) A z → ∀ h:ℕ, legacy Y (i w) (k h) → ‖taking Y H (i w) (k h) (z*(ϕ l)) - vistaTake Y H D' (z*(ϕ l))‖ ≤ propeller l*A
   have he(l n:ℕ): ∀ᶠ w in atTop,P l n w := by
      obtain ⟨S,n',b,h,h',p,t⟩:= Pocket.price_whole K (bk n) (r n) (ϕ l) (Altitude.delimit γ (c l).t (Altitude.short_pinhole (c l).t _))
      filter_upwards [Fashion.wintering Y H D S n' (propeller l/b) (by unfold propeller; positivity)] with w g
      intro A z Hz i k; refine (Fashion.calculation Y H D S n' w i _ g (t _ _ Hz) k).2.1.trans_eq ?_
      field_simp
   obtain ⟨m,k,h⟩:= agenda (fun l i=> extra l i∧∀ j∈ Finset.Iic l,P l j i) (fun l=> (e l).and ((eventually_all_finset _).2 fun n _=> he l n))
   exact ⟨m,k,fun i=> (h i).1,fun l n e=> (h l).2 _ (mem_Iic.mpr e)⟩

structure Buys (c:∀ n,Future Y H j n)(m d:ℕ→ℕ) : Prop extends Subscriber Y H D.toExhibition G j U q x c where
  rowAdv : StrictMono m
  colAdv : StrictMono d
  cone (n : ℕ): legacy Y (i (m n)) (k (d n))
  payHigh (n) : Tapestry.Pay Y (c n).t (i (m n)) (k (d n))
  host (n) : Host Y H (i (m n)) (c n).t (Future.opening Y H j (c n) ∪ Future.closing Y H j (c n))
  growsHost (b s:ℕ): s≤ b → let n:=(c b).t
                            Host Y H (i (m b)) n (Future.opening Y H j (c b) ∪ Future.closing Y H j (c b)∪ volumeAround Λ l (n - (progressBoard s).2) (progressBoard s).1)
  reading (v)(u:v∈FiniteGaugeDataPoly (tent Y H)) : Tendsto (fun n => taking Y H (i (m n)) (k (d n)) (v*Future.boundary Y H j (c n))) atTop (𝓝 ((onDrawing Y H D.univ_ G D.toExhibition j U (SameCharacter.resident Y H D.univ_ G j false (U j) (q.character x))) v))

lemma order_history (q' : Issued Y H D.univ_ G.history G.clipped j false (U j) q) : ∃ c m d, Buys Y H D G j U q x c m d := by
    obtain ⟨c,p⟩:= prepares Y H D' G j U q q' x; clear q'
    let HP(b s n:ℕ) := Host Y H (i n) (c b).t (Future.opening Y H j (c b) ∪ Future.closing Y H j (c b) ∪ volumeAround Λ l ((c b).t-(progressBoard s).2) (progressBoard s).1)
    let P(b n :ℕ) := Host Y H (i n) (c b).t (Future.opening Y H j (c b)∪ Future.closing Y H j (c b)) ∧
     (∀s∈ Finset.Iic b,HP b s n) ∧ ∀ h:ℕ,legacy Y (i n) (k h) → Tapestry.Pay Y (c b).t (i n) (k h)
    have he (b:ℕ) : ∀ᶠ f in atTop,P b f:= ((V).pick.grow_i.tendsto_atTop.eventually (eventually_host Y H _ _)).and (((eventually_all_finset _).2 (fun i _=> (V).pick.grow_i.tendsto_atTop.eventually (eventually_host Y H _ _))).and ((floor_pays Y H V (c b).t).mono fun i p j h=> ⟨(p j h).depth,(p j h).enters⟩))
    obtain ⟨m,a,y,g⟩:= select_rows Y H D j c P he
    obtain ⟨d,t,v⟩:= agenda (fun b h=>legacy Y (i (m b)) (k h)) (by
      intro b -- legacy at stage n' on all h≥m b
      filter_upwards [eventually_ge_atTop (m b)] with h r
      exact (D.status (m b) h).mpr r)
    refine ⟨c,m,d,p,a,t,v,fun i=> (y i).2.2 _ (v i),fun i=> (y i).1,fun i s x=>(y i).2.1 _ (Finset.mem_Iic.mpr x),fun z t=>?_⟩
    obtain ⟨k,C,e⟩:= all_boards K z t
    refine transfer_price (fun n=>propeller n*C) (by simpa using propeller_fades.mul_const C) (p.focus z t) ?_
    filter_upwards [eventually_ge_atTop k] with b r; exact g b k r C z e (d b) (v b)

lemma Buys.pays {m d:ℕ→ℕ}(h: Buys Y H D G j U q x c m d):
    Tendsto (fun n=> taking Y H (i (m n)) (k (d n)) (Future.boundary Y H j (c n))) atTop (𝓝 1):= by
      have he:= h.reading 1 (FiniteGaugeDataPoly K).one_mem
      simp only [one_mul] at he; rw [normalized_draw] at he; exact he
lemma Buys.read {m d:ℕ→ℕ}(h:Buys Y H D G j U q x c m d) {v:Cloud (Dome K)}(p:v∈ FiniteGaugeDataPoly K):
    Tendsto (fun n=> taking Y H (i (m n)) (k (d n)) (v*ϕ n)/ taking Y H (i (m n)) (k (d n)) (ϕ n)) atTop (𝓝 (M v)):= by
    have he: Tendsto (fun n=> taking Y H (i (m n)) (k (d n)) (v*ϕ n)/ taking Y H (i (m n)) (k (d n)) (ϕ n)) atTop (𝓝 (M v/1)):= (h.reading v p).div (h.pays Y H D G j U q x c) one_ne_zero
    rwa [div_one] at he
end purchase
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.order_history
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.Buys.read
