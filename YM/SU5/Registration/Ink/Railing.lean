import YM.SU5.Registration.Ink.Carton
import YM.SU5.Registration.Ink.Breaths
import YM.SU5.FiniteGaugeData.Poin.Alman
/-!
 # Reading the actual positive-pad prices on all the real joint probes
 As a bridge between M5/Rasp/ & this contour.
 Reuse C23/ heat estimates, Poin.baroque & Rail.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SatinWFixed.Carton
open Filter Function Set MeasureTheory Spectral Mink Boundary Boundary.Small OS Complex OS.Semigroup
open CF.Buffered.Afterglow.Hierarchy.Seld Poin
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder
variable {H:Hilbert}{S:OS.Semigroup H timeAxis}{V : Type*} [AddCommGroup V] [Module ℂ V] {n:ℕ}
variable (B: Carton S V)
lemma rip_shift (w : ℂ) (p : ℝ≥0) (x : Space3) (b : E4) (v : H) (h : (p:ℝ)<w.im) :
    ripZ S (w+(YM.time b:ℂ)) p (x+spatial b) v = S.unit.translation b (ripZ S w p x v) := by
  have he := (Small.down ..).2 h
  have ht : Small.interval (w+(YM.time b:ℂ)) p = Small.interval w p + OS.Semigroup.sideways (YM.time b) := by
    unfold Small.interval OS.Semigroup.sideways; ring
  have hu : bufferF (x+spatial b) = OS.Semigroup.SEP timeAxis b + bufferF x := by
    apply Subtype.ext
    change position (x+_) 0 = (b-YM.time b • basis _) + position x 0
    apply Mink.ext_by <;> simp [sub_eq_add_neg,add_comm]
  have hh q : S.F (Small.interval w p) (S.U (OS.Semigroup.SEP timeAxis b) q) =
      S.U (OS.Semigroup.SEP timeAxis b) (S.F (Small.interval w p) q) :=
    DFunLike.congr_fun (S.stays he _) q
  change S.F _ (S.U _ v) = S.edge (YM.time b) (S.U _ (S.F _ (S.U _ v)))
  rw [hu,S.space,ht,← S.along he]
  simp only [ContinuousLinearMap.comp_apply, hh]

private lemma heated_rip {y:ℝ} {p:ℝ≥0} (t : (p:ℝ) < y) : let r:= y-(p:ℝ);
 ripZ S (↑y*I) p 0=S.E r.toNNReal:=by
 let r:= y-(p:ℝ); have h:0<r:= sub_pos.mpr t
 have he: bufferF 0=0:= Subtype.ext (by apply Mink.ext_by <;> simp [bufferF]) -- ◎ check
 change _= S.E r.toNNReal;
 unfold ripZ; rw [he,S.uZero,ContinuousLinearMap.comp_id];
 have hp: interval (↑y*I) p=duration r.toNNReal:=by apply Complex.ext <;> simp [Small.interval, duration,Real.coe_toNNReal r h.le]; rfl
 rw [hp,S.roots_heat (Real.toNNReal_pos.mpr h)]
abbrev fareGap (y:Heights n) (p:ℝ≥0)(i j:Fin n): ℝ≥0:= Real.toNNReal (y j-y i-(p+p:ℝ≥0))
lemma ripZ_gap (p:ℝ≥0) (y:Heights n) (x:Points n) (i j:Fin n)(u: ((p+p:ℝ≥0):ℝ)<y j-y i) :
  ripZ S (shift x y j-shift x y i) (p+p) (trace x j - trace x i)= S.E (fareGap y p i j)* M S (x j - x i):=by
 let d:=x j-x i; have hg:= SatinRegistration.heat_commutes S (fareGap y p i j) d
 rw [hg.eq]; ext1 w
 change _ = M S d _
 have h: ((p+p:ℝ≥0):ℝ) < ((↑(y j-y i):ℂ) * I).im:=by simpa using u
 have hT: shift x y j-shift x y i= ↑(y j-y i)*I+(YM.time d:ℂ):=by simp only [d,Boundary.shift, show YM.time (x j-x i)=YM.time (x j) - YM.time (x i) from rfl,ofReal_sub]; ring 
 have hS: trace x j-trace x i=0+ spatial d:=by rw [zero_add]; rfl
 rw [hT,hS,rip_shift _ _ _ d w h, heated_rip u]; rfl -- wrap heat

lemma matrix_film (p:ℝ≥0) (v:Fin n→V)(z:Times n)(x:SpacePoints n):
  B.matrixZ p n z x v= inner ℂ B.omega ((Rail (fun i=> B.bar p (v i)) (fun i j=>ripZ S (z j-z i) (p+p) (x j-x i))) B.omega):=by
 cases n with
 | zero=> rfl
 | succ n=>
  suffices h : B.bar p (v 0) (B.trainZ p n (Fin.tail z) (Fin.tail x) (Fin.tail v) (z 0) (x 0))=(Rail (fun i=> B.bar p (v i)) (fun i j=> ripZ S (z j-z i) (p+p) (x j-x i))) B.omega from congrArg _ h
  induction n with
  | zero=> rw [Rail_step,s1P,mul_one]; rfl  -- ⚠ not rfl bc `A *1` at argument.OK? likely rfl
  | succ n ih=>
    nth_rw 1 [Rail_step]
    rw [s1S];
    let v':=Fin.tail v; let z':= Fin.tail z; let x':= Fin.tail x;
    change B.bar p (v 0) (ripZ S (z' 0-z 0) (p+p) (x' 0-x 0) (B.bar p (v' 0) (B.trainZ p n (Fin.tail z') (Fin.tail x') _ (z' 0) (x' 0))))=_
    rw [ih]; rfl -- implicit replace
private lemma Film_order {R:Type}[Monoid R]{α:Type}(X:α→R)(J K:α→α→R){r:α→α→Prop}(h:∀ i j,r i j→ J i j= K i j)(L:List α)(t:L.Pairwise r) : Film X J L = Film X K L:=by
 induction L with
 | nil=> rfl
 | cons i l ih=> rw [Film_step,Film_step, ih t.of_cons]; congr 2; cases l with
                                                                      | nil => rfl
                                                                      | cons j l=> exact h i j ((List.pairwise_cons.mp t).1 j (List.Mem.head ..))
lemma film_record (p:ℝ≥0) (v:Fin n→V)(y:Heights n)(u : enough y p) (x:Points n):
  B.matrixZ p n (shift x y) (trace x) v= inner ℂ B.omega ((pitch S (fun i=> B.bar p (v i)) (fun i j=> S.E (fareGap y p i j)) x) B.omega):=by
 let F(i):= B.bar p (v i); let D(i j:Fin n):= S.E (fareGap y p i j)
 rw [B.matrix_film]
 change _=inner ℂ _ (Film (fun i=> optx S (F i) (x i)) D (Each n) B.omega)
 rw [baroque S B.omega F _ (fun x=>B.stay x) D (fun x i j=> (SatinRegistration.heat_commutes S _ x).symm)] -- binder order peek
 congr 2
 refine Film_order F _ _ (r:=fun i j=>i<j) (fun i j h=>?_ ) (Each n) ?_ -- may need unfold Rail
 · refine ripZ_gap p y x i j ?_; push_cast; linarith [u.2.2 i j h,p.coe_nonneg]
 refine List.pairwise_lt_finRange n

variable {F:InkWaves V} (hF:B.Defined F)
include hF
lemma sees_wave (p:ℝ≥0)(v:Fin n→V)(y:Heights n)(u:enough y p)(x:Points n):
 F.restricted v y x= inner ℂ B.omega (pitch S (fun i=> B.bar p (v i)) (fun i j=> S.E (fareGap y p i j)) x B.omega):=by
 have hp:lit (Boundary.shift x y) p:=by simpa [lit,Boundary.shift] using u
 rw [InkWaves.restricted,hF n _ (Work.C03.lit_strict hp) p hp, film_record B p v y u]
lemma reading_tensor (p:ℝ≥0)(v:Fin n→V)(f:Fin n→Test4)(y:Heights n)(u:enough y p):
 F.psi v y (Joint.materialize n f) = inner ℂ B.omega ((Rail (fun i=> valise S (B.bar p (v i)) (f i)) (fun i j=> S.E (fareGap y p i j))) B.omega):= by
 rw [←orches S B.omega B.omega (fun i=> B.bar p (v i)) (fun i j=> S.E (fareGap y p i j)) f]
 unfold InkWaves.psi
 apply integral_congr_ae
 filter_upwards with x
 unfold concert
 rw [sees_wave B hF p v y u x,mul_comm]
end YM.SatinWFixed.Carton
