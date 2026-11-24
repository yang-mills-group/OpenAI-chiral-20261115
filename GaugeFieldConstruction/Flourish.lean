import GaugeFieldConstruction.Dawes
/-!
# exchange derivatives in separate external pair locations.
-/
set_option autoImplicit false
set_option maxHeartbeats 40000
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
attribute [local instance] opCStarAlgebra
open AnalyticBridge VerifiedReset Taxi
open Lenten
open Stationary Vault Font
open Bank Laurent Bloch Tap Hove Spire
open Haro Peaks Rush Fir Next.Free Thorn
open Planned.PrimaryIntegral295 Carrier
namespace Boom
variable {f:Side} {M:Male}{U Q:Op (Single f)}{o:Skye.Seat f}{h:ℝ}{r:ℕ}
variable (p: SentK o Q)(u:quote_B M Q o h r)(e:100<f.val)(w:h≠0)
abbrev RedV (r:ℕ)(o: Skye.Seat f)(M:Male)(b:Bool)(k:Plane)(i:Kt)(x: Single f):= Lψε r M b k i (spot o x.1.1) (portB x)
abbrev Lnode(r:ℕ)(M:Male)(b:Bool)(V:Views): Lattice.Cover→ Kt→ Kt→ℂ:= fun x i j=> Lψε r M b (kview b V) i x j
lemma zero_PJl (t: Fn f): PJ_act Q o 0 t=0:=by simp [PJ_act] -- tune binder Fn
lemma zero_PJr (v: Fn f): PJ_act Q o v 0=0:=by simp [PJ_act]
lemma starTier {f:ℝ→ℂ}{x y z:ℂ}(h:TierS f x y z): TierS (fun i=>star (f i)) (star x) (star y) (star z):= h.map (starL' ℝ:ℂ≃L[ℝ]ℂ).toContinuousLinearMap
private abbrev PN (a b:Kt)(x y:Plane)(i j:ℕ) :ℂ:=PJ_act Q o (RedV i o M false x a) (RedV j o M true y b)
include p u e w
set_option maxHeartbeats 100000 in
lemma team_Q (a b:Kt)(x y:Plane) : let J:= PN (Q:=Q) (M:=M) (o:=o) a b x y; (0 < r→ J 0 0=0) ∧ (1<r→ J 1 0 + J 0 1=0)∧(2<r → J 2 0 + J 0 2 + (J 1 1 + J 1 1)=0):=by
 let s:= (x,y); let F₁(t:ℝ)(i:Single f):= candle M o false (t • s) i a; let F₂(t:ℝ)(i:Single f):= candle M o true (t • s) i b; intro J
 let X(i:Single f × Single f)(t:ℝ):= star (F₁ t i.1)*HyT o Q i.1 i.2 *F₂ t i.2; let A(i j:ℕ)(k: Single f×Single f):=star (RedV i o M false x a k.1)*HyT o Q k.1 k.2 * RedV j o M true y b k.2
 have he(i j): J i j=∑ k:Single f ×Single f, A i j k:= rfl
 have ht (k: Single f×Single f): TierS (X k) (A 0 0 k) (A 1 0 k+A 0 1 k) (A 2 0 k+A 0 2 k+(A 1 1 k+A 1 1 k)):=by
    have hf:= ((starTier (αcharge (M:=M) (b:=false) k.1 (x,y) o a)).mul (TierS.const (HyT o Q k.1 k.2))).mul (αcharge (M:=M) (b:=true) k.2 (x,y) o b)
    simp only [mul_zero,zero_add,add_zero] at hf; exact hf -- tune binder order maybe `i k j x` omitted
 have hx: TierS (fun t=> PJ_act Q o (F₁ t) (F₂ t)) (J 0 0) (J 1 0+ J 0 1) (J 2 0+J 0 2+(J 1 1+J 1 1)):=by
    simp_rw [he,← sum_add_distrib]; let he:= TierS.sum X (A 0 0) (A 1 0+ A 0 1) (A 2 0 + A 0 2 +(A 1 1+A 1 1)) univ (fun i _=>ht i); have hv(t): (fun t:ℝ=> PJ_act Q o (F₁ t) (F₂ t)) t=(∑ i: Single f×Single f, X i) t:=by rw [Finset.sum_apply]; rfl
    -- already matched derivative amounts
    rw [funext hv]; exact he -- tune
 exact Account_F Q o h M u p e w a b s hx
omit p u e w
lemma Red0 (t:Plane)(b:Bool)(i:Kt) : RedV 0 o M b t i= RedV 0 o M b 0 i:=by funext x; unfold RedV Lψε; congr 1
lemma Redζ(k:ℕ)(p:0<k)(b:Bool)(i:Kt): RedV k o M b 0 i=0:=by
 funext j; unfold RedV; rw [Ω_root]; simp [δbook,p.ne']
include p u e w
lemma alone_Φ (a b:Kt)(x y:Plane) (i j:ℕ)(t:r≤3)(v:i+j<r): PJ_act Q o (RedV i o M false x a) (RedV j o M true y b)=0:=by
 let L:= PN (o:=o) (M:=M) (Q:=Q);
 have ht:= team_Q p u e w a b x y
 have hv(k) (p:k=1∨ k=2)(u:k<r) (a b:Kt) (x y:Plane): L a b x y k 0=0 ∧ L a b x y 0 k=0:=by
    -- shadow p/u bad
    have he:= team_Q (o:=o) ‹SentK o Q› ‹quote_B M Q o h r› e w a b x 0
    have hz:= team_Q (o:=o) ‹SentK o Q› ‹quote_B M Q o h r› e w a b 0 y
    rcases p with rfl|rfl
    · have hx:= he.2.1 u; have hs:= hz.2.1 u; dsimp only [PN,kview] at hx hs ⊢ -- unfold L
      unfold L PN
      rw [Redζ 1 Nat.zero_lt_one, zero_PJr,add_zero] at hx
      rw [Redζ 1 Nat.zero_lt_one,zero_PJl,zero_add] at hs
      rw [Red0 x false, Red0 y true]; exact ⟨hx,hs⟩ -- tune binder order
    have hx:= he.2.2 u; have hs:= hz.2.2 u; dsimp only [PN] at hx hs; unfold L PN
    simp_rw [Redζ 1 Nat.zero_lt_one, Redζ 2 (by decide),zero_PJr,add_zero] at hx
    simp_rw [Redζ 1 Nat.zero_lt_one, Redζ 2 (by decide),zero_PJl,zero_add,add_zero] at hs
    rw [Red0 x false, Red0 y true]; exact ⟨hx,hs⟩
 rcases show (i=0∧j=0) ∨ ((i=1∨i=2)∧j=0) ∨ (i=0∧(j=1∨j=2)) ∨(i=1∧j=1) by omega with ⟨rfl,rfl⟩ | ⟨g,rfl⟩| ⟨rfl,g⟩|⟨rfl,rfl⟩
 · exact ht.1 v
 · exact (hv i g (by omega) a b x y).1
 · exact (hv j g (by omega) a b x y).2
 let P:=L a b x y; have hh:= ht.2.2 v; change P 2 0 + P 0 2 +(P 1 1+ P 1 1)=0 at hh; unfold P at hh; rw [(hv 2 (by omega) v a b x y).1, (hv 2 (by omega) v a b x y).2,zero_add,zero_add,← two_mul] at hh -- tune rewrite P
 exact (mul_eq_zero.mp hh).resolve_left two_ne_zero
end Boom
end YM.CF.TableF
end
