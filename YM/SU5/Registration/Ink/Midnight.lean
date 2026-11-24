import YM.SU5.Registration.Ink.Railing
import YM.SU5.Registration.Ink.Appointment
import YM.SU5.Registration.RapidBoundary
import YM.SU5.Registration.Ink.Shiny

/-!
 # Finishing at the absolute corner: actual field on G buys it
 SO: norms here in all time-energy powers on this character. No extra momentum hypothesis
 yet. Keep positive Eu-cut rates at each occurrence.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SatinWFixed
open Filter Function Set MeasureTheory Spectral Mink Boundary Boundary.Small OS Complex OS.Semigroup
open CF.Buffered.Afterglow.Hierarchy.Seld Poin SatinRegistration
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder
variable {H:Hilbert}{S:OS.Semigroup H timeAxis}{V : Type*} [AddCommGroup V] [Module ℂ V] {n:ℕ}
variable (B: Carton S V)
abbrev MarkType (V:Type*):= V × Test4
abbrev MarkWords (V:Type*):= List (MarkType V)
namespace Carton
local notation "T"=> S.E
local notation "D"=> radial S
abbrev vacuum : D:= ⟨B.omega,B.hot 1 ▸ heat_domain S B.omega (s:=1) zero_lt_one⟩
noncomputable abbrev black (v:V)(f:Test4) : @DOp _ _ S:= field S _ (B.coherent v) (B.price v) f
noncomputable abbrev blue (v:V)(p:ℝ≥0)(f:Test4) : @DOp _ _ S:= warm S (B.bar p v) f
lemma blue_apply (v:V)(p:ℝ≥0)(f:Test4)(x:D): (B.blue v p f x).1=valise S (B.bar p v) f x.1:= warm_actual ..
lemma blue_stove(v:V)(p:ℝ≥0) (u:0<p)(f:Test4)(x:D): B.blue v p f x= stoveAt S p (B.black v f (stoveAt S p x)):=by
 refine Eq.trans ?_ (exact_stove S _ (B.coherent v) (B.price v) u u f x); unfold bothPads; simp only [min_self,tsub_self,S.eZero]; rfl
lemma blue_finish (v:V)(f:Test4){ι:Type*}(l:Filter ι)(p:ι→ℝ≥0)(t:Tendsto p l (𝓝[>] 0)){F:ι→D}{x:D}(u:(bands S).Approaches l F x) :
  (bands S).Approaches l (fun i=> B.blue v (p i) f (F i)) (B.black v f x):=by
 have he:= passes_lim S _ (B.coherent v) (B.price v) l f p p t t u
 unfold bothPads at he; simp only [min_self,tsub_self,S.eZero] at he; exact he
-- Domain Rail actions at positive internal pad and potentially dynamic heat gaps. No limit motions.
variable (v:Fin n→V)(f:Fin n→Test4)(J:Fin n→Fin n→ℝ≥0)(F:Fin n→ℝ≥0)
noncomputable abbrev lateFilm:= Film (fun i=> B.blue (v i) (F i) (f i)) (fun i j=> stoveAt S (J i j))
noncomputable abbrev darkFilm:= Film (fun i=> B.black (v i) (f i)) (fun i j=>stoveAt S (J i j))
lemma tonight (L:List (Fin n))(x:D) : (B.lateFilm v f J F L x).1=
  (Film (fun i=> valise S (B.bar (F i) (v i)) (f i)) (fun i j=> S.E (J i j)) L) x.1:=by
 induction L with
 | nil=> rfl
 | cons i l ih=>
    cases l with
    | nil=> exact blue_apply ..
    | cons j l=>
        change (B.blue (v i) (F i) (f i) (stoveAt S (J i j) (B.lateFilm v f J F (j::l) x))).1=_
        rw [blue_apply]; unfold stoveAt; change valise S (B.bar (F i) (v i)) (f i) (T (J i j) (B.lateFilm v f J F (j::l) x).1)= _; rw [ih]; rfl
lemma morning (L:List (Fin n)) {ι:Type*}(l:Filter ι)(U:ι→ Fin n → ℝ≥0)(t:∀ i,Tendsto (fun k=>U k i) l (𝓝[>] 0))(W:ι→ Bin n ℝ≥0)(w:∀ i j,Tendsto (fun k=> W k i j) l (𝓝 (J i j))) {P:ι→D}{x:D} (g:(bands S).Approaches l P x): (bands S).Approaches l (fun i=>B.lateFilm v f (W i) (U i) L (P i)) (B.darkFilm v f J L x):=by
 induction L with
 | nil=> exact g
 | cons i L ih=>
    cases L with
    | nil=> exact blue_finish B _ _ l _ (t i) g
    | cons j L'=> exact blue_finish B _ _ l _ (t i) (through_heat S l _ (w i j) ih)
noncomputable abbrev activate (p:MarkType V) := B.black p.1 p.2
noncomputable def realWork (Q:MarkWords V): @DOp _ _ S := (Q.map (B.activate)).prod
noncomputable def row (Q:MarkWords V): D:= B.realWork Q B.vacuum
lemma play (L:List (Fin n)) : B.darkFilm v f 0 L=B.realWork (L.map fun i=>(v i,f i)) :=by
 induction L with
 | nil=> rfl
 | cons i L ih=>
    unfold darkFilm Film realWork; rw [show Film (fun i=> B.black (v i) (f i)) _ L=B.realWork (L.map fun i=>(v i,f i)) from ih,List.map_cons,List.map_cons,List.prod_cons];
    change _*(clip (fun (_ _ :Fin n) =>stoveAt S 0) i L * (B.realWork (L.map fun i=>(v i,f i))))= B.black (v i) (f i)* (B.realWork (L.map fun i=>(v i,f i)))
    suffices clip (fun (_ _ :Fin n) =>stoveAt S 0) i L=1 by rw [this,one_mul]
    cases L with
    | nil=> rfl
    | cons j l=> ext1 x; exact stoveAt_zero S _
variable {R:InkWaves V} (p:B.Defined R) {W:WView V} (e:R.NonTangentialFree W)
include p
lemma reading_y (s:ℝ≥0) (y:Heights n) (h:enough y s): R.psi v y (Joint.materialize n f)= inner ℂ B.omega (B.lateFilm v f (fareGap y s) (fun _=>s) (Each n) B.vacuum).val:=
 (B.reading_tensor p s v f y h).trans ((congrArg (inner ℂ B.omega) (tonight B v f (fareGap y s) (fun _=>s) (Each n) B.vacuum)).symm)
include e
lemma reality_tensor : W.W n v (Joint.materialize n f)= inner ℂ B.omega (B.row (List.ofFn fun i=>(v i, f i))).1:=by
 let u:= (𝓝[>] (0:ℝ≥0)); have u':u.NeBot:=inferInstanceAs (𝓝[>] (0:ℝ≥0)).NeBot
 let g(t:ℝ≥0):=8*(t:ℝ); let y(t:ℝ≥0):= g t • (rate n); have t(s:ℝ≥0)(u:0<s): y s ∈ east n:=by
    simpa only [zero_add] using dawns (light n) (mul_pos (by norm_num : (0:ℝ)<8) (show (0:ℝ)<(s:ℝ) from u))
 have ht: ∀ᶠ s in u, enough (y s) s:=by
    filter_upwards [self_mem_nhdsWithin, (gt_mem_nhds (show (0:ℝ≥0)<1 by norm_num)).filter_mono nhdsWithin_le_nhds] with s h p
    have hp:0<(s:ℝ):=h; have hb := (show broad (y s) (g s) from (zero_add (y s)) ▸ begins (light n) (g s) (mul_nonneg (by norm_num : (0:ℝ)≤8) hp.le))
    exact ⟨h,p,fun i j k=> lt_of_lt_of_le (show 4*(s:ℝ)<g s by dsimp only [g]; linarith) (hb _ _ k)⟩ -- `p: setOf`, etc
 have yC:Continuous y:=by unfold y g; fun_prop
 have hy:y 0=0:= by simp [y,g]
 have hm:Tendsto y u (𝓝[east n] 0):= tendsto_nhdsWithin_iff.mpr ⟨(hy ▸ yC.continuousAt.tendsto).mono_left nhdsWithin_le_nhds,Eventually.mono self_mem_nhdsWithin (fun i p=> t i p)⟩
 have hv (i j: Fin n): Tendsto (fun s=> fareGap (y s) s i j) u (𝓝 0):=by
    have hc: Continuous (fun s=> fareGap (y s) s i j):= continuous_real_toNNReal.comp (by unfold y g; fun_prop)
    exact (show fareGap (y 0) 0 i j=0 by rw [hy,fareGap]; simp) ▸ (hc.tendsto 0).mono_left nhdsWithin_le_nhds
 have hu := B.morning v f (J:=fun _ _=>0) (Each n) u (fun s _=>s) (fun _=> tendsto_id) (fun s=>fareGap (y s) s) hv (show (bands S).Approaches u (fun _=> B.vacuum) B.vacuum from (?_))
 swap; · intro k; simp only [sub_self,Grading.budget,Grading.due,map_zero,norm_zero,mul_zero,tsum_zero]; exact tendsto_const_nhds
 rw [show (B.row _) = _ from (show B.row (List.ofFn fun i=>(v i, f i))=B.darkFilm v f 0 (Each n) B.vacuum from (?_))]; rotate_left
 · unfold Each; rw [play]; rw [← List.ofFn_eq_map]; rfl
 let X(s:ℝ≥0):= inner ℂ B.omega (B.lateFilm v f (fareGap (y s) s) (fun _=>s) (Each n) B.vacuum).1; have he := tendsto_nhds_unique_of_eventuallyEq (show Tendsto (fun s=> R.psi v (y s) (Joint.materialize n f)) u _ from (e.corner n v (Joint.materialize n f)).comp hm) (show Tendsto X u _ from (tendsto_const_nhds (x:=B.omega)).inner (Grading.Approaches.hilbert (bands S) hu)) (ht.mono (fun s hu=> B.reading_y v f p s (y s) hu))
 exact he
end Carton
end YM.SatinWFixed
