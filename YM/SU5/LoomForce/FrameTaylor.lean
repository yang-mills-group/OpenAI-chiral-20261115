import YM.SU5.LoomForce.SymAperture
import YM.SU5.WindTorque.Docket
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.LitCurrent.Surplus
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour
open Stax Skye Jet Scroll Finset Palot Cadre Vow RG Rive Nor Hake MeasureTheory
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical ContDiff
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel Swell StressExchange
variable {N:Side}{P T:SOp N}{a b d v g t u:ℝ}{r k:ℕ}
open Next.Rank Next.Rank.Spindle
open CF.Pannier.Chancel.Rous
variable (B:ℕ)
abbrev FrameA (B:ℕ) := Next.Rank.Spindle.Turn B→SU.group.Color
local notation "M"=> More N
local notation "A"=> tangD N
variable (o : Seat N)
-- all directions on exponentially numerous modes, controlled by sup irrespective of
-- torus size.
def install : Next.Rank.Spindle.Space group o B →L[ℝ] A:=
 ({ toFun := fun x i => if h:i∈Next.Rank.Spindle.Room o B then x ⟨i,h⟩ else 0
    map_add' :=fun x y => funext fun i=>by dsimp; split <;>simp [*]
    map_smul' :=fun c x=> funext fun i=>by dsimp; split <;>simp [*]
       : Next.Rank.Spindle.Space group o B →ₗ[ℝ] A}).toContinuousLinearMap

lemma stage_add (p:Word B)(x y: FrameA B) : Spindle.stage p (x+y)=Spindle.stage p x + Spindle.stage p y := by
 induction p with
 | nil => simp [Spindle.stage]
 | cons i l ih=>
     simp only [Spindle.stage,List.map_cons,List.sum_cons] ; unfold Spindle.stage at ih; rw [ih]; rw [add_add_add_comm (if i.2 then -x i.1 else x i.1)]; refine congrArg₂ (·+·) ?_ rfl
     split <;> simp [add_comm]

lemma stage_scaled (p:Word B)(s:ℝ)(x:FrameA B) : Spindle.stage p (s • x)=s • Spindle.stage p x := by
 induction p with
 | nil => simp [Spindle.stage]
 | cons i l ih=> simp only [Spindle.stage,List.map_cons,List.sum_cons,smul_add] ; unfold Spindle.stage at ih; rw [ih]; split <;> simp
def collectF (h:2*(B+1)<(More N).val) : FrameA B→L[ℝ] Next.Rank.Spindle.Space group o B :=
 ({ toFun x i:= Spindle.stage (word group h i) x
    map_add' x y:=funext fun i=> stage_add B (word group h i) x y
    map_smul' z x:=funext fun i=> stage_scaled B (word group h i) z x : FrameA B→ₗ[ℝ] Next.Rank.Spindle.Space group o B}).toContinuousLinearMap
lemma collect_price (h:2*(B+1)<(More N).val) (x:FrameA B) : ‖collectF B o h x‖ ≤ 4*B*‖x‖ := by
 apply (pi_norm_le_iff_of_nonneg (by positivity:(0:ℝ)≤4*B*‖x‖)).mpr; intro i
 have hx (L:Word B) : ‖Spindle.stage L x‖ ≤ L.length*‖x‖:=by
   induction L with
   | nil=> simp [Spindle.stage]
   | cons i L ih=>
      unfold Spindle.stage; rw [List.map_cons,List.sum_cons,List.length_cons]; unfold Spindle.stage at ih
      refine (norm_add_le ..).trans ((add_le_add (b:=‖x‖) ?_ ih).trans (Eq.le ?_))
      · split; rw [norm_neg]; exact norm_le_pi_norm x i.1; exact norm_le_pi_norm x i.1
      push_cast; ring
 exact (hx (word group h i)).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast lengths_word group h i) (norm_nonneg _))
lemma install_price (x:Next.Rank.Spindle.Space group o B) : ‖install B o x‖ ≤ ‖x‖ := by
 refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (fun i=>?_)
 change ‖(if h:i∈_ then x ⟨i,h⟩ else (0:group.Color))‖≤_; split; next e=> exact norm_le_pi_norm x ⟨i,e⟩
 rw [norm_zero]; exact norm_nonneg _

lemma arrivals (x:Cover)(w:Lattice.Walk): (visits x w).map (fun v=>wrap (More N) v+o)=visits (wrap (More N) x+o) w:=by induction w generalizing x with|nil=>simp [visits]|cons i w ih=>simp [visits,ih,wrap_vec,add_right_comm]
def armFace (o:Seat N)(i:Turn B) : Face (Per (More N)) := (wrap _ i.val.1+o,i.val.2)
lemma touches (i:Turn B) : touched (armFace B o i) ⊆ Spindle.patch B o := by
 unfold armFace touched; simp only [←arrivals]; intro x v
 obtain ⟨y,e,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp v); exact village_le _ (face_patch i y e)

abbrev paintedMark (U:Pane N) (ρ:ℝ) (i:Turn B) := ρ • group.curvature (registered B U o i)
abbrev receiveMark (U:Pane N) (ρ:ℝ) (i:Turn B) := ρ • group.curvature (faceValue U (armFace B o i))

-- Estimate for the gauge-fixed doll read: also compare the aperture's true price
-- to the plain unrotated material, by *WellDrawn* cost. (No label transport assumed at tangents)
variable (h: 2*(B+1)< (More N).val)(V:Rules SU.group)
include h
lemma frame_exact (U:Pane N) (hc:Healthy t (Spindle.patch B o) U)(t0:0<t)(e: 4*B*t≤ V.c):
    let X := install B o (wired 1 o B U)
    Agrees (Spindle.patch B o) (spine U o) (increment 1 X) ∧
      ‖X‖ ≤ 2*(4*B*t) ∧
      ‖X-install B o (collectF B o h (paintedMark B o U 1))‖≤ (V.C+SU.group.colorScale)*(4*B*t)^2 := by
 intro X
 obtain ⟨a,b,c⟩:= Spindle.closer V h U hc 1 zero_lt_one t0 e
 rw [div_one] at a c; let G:= SU.group
 refine ⟨fun i x y=>?_,(install_price B o _).trans a,le_trans ?_ c⟩
 · let u : Dim o B := ⟨i, mem_filter.mpr ⟨mem_univ _, x, y⟩⟩; specialize b u
   change _= G.lieExp _* 1; rw [mul_one]; apply Eq.trans b.symm
   change G.lieExp (1 • wired 1 o B U u) = G.lieExp (if h:i∈_ then wired 1 o B U ⟨i,h⟩ else 0)
   rw [one_smul,dif_pos u.property]
 let W:= paintedMark B o U 1; rw [show X-_= install B o (wired 1 o B U -collectF B o h W) from (map_sub ..).symm]; apply (install_price ..).trans; rw [show collectF B o h W= rows 1 h (G.curvature ∘ registered B U o) from ?_]
 funext i; rw [rows,inv_one,one_smul]; apply congrArg (Spindle.stage _); ext1 i; change paintedMark B o U 1 i= group.curvature _; unfold paintedMark; rw [one_smul]

omit h in
lemma permit_walk (U:Pane N)(y:Site (More N))(p:y∈ Spindle.patch B o)(f:Tiny (Spindle.patch B o) U v)(q:0 ≤ v) : SU.group.chord (fingers U o y) ≤ (4*B)*v:=by
 let x:=lift (y-o); have he:x∈box B:=Work.E08.lift_mem_box ((doors y).1 p)
 let w:=paths x
 have ht(a)(hx:a ∈ visits o w): a∈ Spindle.patch B o := by
    have ht:=arrivals o 0 w; rw [map_zero,zero_add] at ht; rw [←ht] at hx
    obtain ⟨z,v,rfl⟩:=List.mem_map.mp hx; exact village_le z (village x he _ v)
 have hu:fingers U o y=travel U o w:=by
    change travel _ _ (paths x)= _; rw [travel_at]; simp; rfl
 rw [hu]; refine (Buffered.EmberWind.Staff.held_peace N U _ w o f ht).trans (mul_le_mul_of_nonneg_right (by rw [show List.length w=_ from lengths x]; exact_mod_cast bounded he) q)

lemma receive_cost (U:Pane N)(hc:Healthy t (Spindle.patch B o) U)(f:Tiny (Spindle.patch B o) U v)(q:0≤v){x:Turn B} :
    ‖paintedMark B o U 1 x-receiveMark B o U 1 x‖ ≤ 2*group.colorScale*(4*B*v)*t ∧
    ‖paintedMark B o U 1 x‖ ≤ t ∧ ‖receiveMark B o U 1 x‖ ≤ t := by
 let k:= armFace B o x; let w:= faceValue U k; let Y:= fingers U o k.1
 have hp: registered B U o x = Y*w*Y⁻¹:= by rw [registering B U h]; exact face_gauge _ _ k
 have hu:= chords B U t hc h x; rw [hp,Gauge.chord_conj] at hu
 have he:= (Gauge.curvature_norm group w).trans hu; have hx:= permit_walk B o U _ (touches B o x (Work.E01.base_touched k)) f q
 simp only [paintedMark, receiveMark, one_smul,hp]
 change ‖group.curvature (Y*w*Y⁻¹)-group.curvature w‖≤ _ ∧ _ ∧ _
 rw [Gauge.curvature_conjugate]; refine ⟨(Next.Fluctuations.adjoint_norm_sub ..).trans ?_,by rw [Gauge.norm_adjoint]; exact he, he⟩; have hv:= group.colorScale_pos; exact mul_le_mul (mul_le_mul_of_nonneg_left hx (by positivity)) he (norm_nonneg _) (by positivity)

open Urn Salt
variable {p:BudgetPoint}{K:Scree.Loom N}{e:ℝ}{q:ℕ} (x:Site N)(z:Checked p K e d a k q)(E:Pattern P T r d a v)
variable (bP: p.B=B)
local notation "Τ" => p.threshold
local notation "ℓ" => occupancy a v g
local notation "Λ" => HopeT d b g 3
local notation "τ" => (Surplus.tax K p x k E)
local notation "S" => (offsetMask p.B x)
local notation "ξ" => node x
local notation "λp" => 4* (B:ℝ)
-- canonical aperture even when no tag licensed -- give zero output on failure.
local notation "TX" => taxpayer x E (k:=k)
include z E h
variable (W:TankSpot d u)(Q: HopeT d b g 3)
omit h in
lemma stencil_cost (x:Site N) (Q:HopeT d b g 3): 0≤ occupancy a v g:= (occupied (E.A x) (E.moorA x) z.hint z.angle (k:=k) Q (guard0 (half_pos z.angle).le)).nonneg
structure Mantle (V : Rules SU.group) (B :ℕ)(p u:ℝ) : Prop where
 snow : 4*B*p ≤ V.c
 door : 2*(4*B*p) ≤ u

variable (A':Mantle V B p.threshold u) (U: Pane N)
local notation "J"=>install B (node x) ∘L collectF B (node x) h
local notation "Φ"=> install B (node x) (wired 1 (node x) B U)
local notation "doll"=> untouched (E.A x)
include bP V W A'
lemma permit_trace (f:pingS Τ S U) : Healthy Τ (Spindle.patch B ξ) U ∧ ‖Φ‖≤2*(4*B*Τ) ∧ τ U=doll k (increment 1 Φ) ∧ ‖Φ-J (paintedMark B ξ U 1)‖≤ (V.C+SU.group.colorScale)*(4*B*Τ)^2:= by
  let X:=install B ξ (wired 1 ξ B U)
  have hx:S=Spindle.patch B ξ:= by unfold offsetMask; rw [bP]; rfl
  have ht: Healthy Τ (Spindle.patch B ξ) U:= hx ▸ ping_le f
  obtain ⟨c,y,g⟩:= frame_exact B ξ h V U ht p.threshold_pos A'.snow
  let P':= increment (1:Pane N) X; have hu:= W.paid N X (le_trans y A'.door)
  refine ⟨ht,y,?_,g⟩
  rw [← tax_invariant x z E (fingers U ξ)]
  have h': k≤ B:= by have ht:=z.extra; omega
  refine tax_degree x z E (spine U ξ) _ ((pingB ..).2 f) ?_ (agrees_mono c (Corona.halo_mono h' (Subset.refl _)))
  exact ⟨fun s i j g=>(hu.1 s i j g).trans (half_le_self z.angle.le), fun s i j g=>(hu.2 s i j g).trans (half_le_self z.angle.le)⟩

-- before making the Paint claim, have this sup at every actual depth including beyond gates
abbrev broadCash (V:ℝ)(L:ℝ):= V*(2*L)^3+(2:ℝ)⁻¹*V*(2*L)^2
abbrev rawError (V:Rules SU.group)(L:ℝ)(B:ℕ)(t α:ℝ):ℝ :=
    (V.C+group.colorScale)*L^2+4*B*(2*group.colorScale*(4*B*α)*t)
abbrev broadError (C L:ℝ) (a:ℝ):= C*(2*L)^3+(2:ℝ)⁻¹*C*a*(2*L+L)
include Q
lemma inBasket : ‖τ U‖ ≤ broadCash ℓ (λp * Τ) := by
  have ht:=p.threshold_pos
  let t:=4*(B:ℝ)*Τ; have hv:0≤t:=by unfold t; positivity
  have hp:= stencil_cost z E x Q
  by_cases f:pingS Τ S U; swap
  · change ‖(live K p k x (E.A x) U).trace‖≤_; rw [live, Set.indicator_of_notMem f,Matrix.trace_zero, norm_zero]; unfold broadCash; positivity
  obtain ⟨-,y,g0,-⟩:= permit_trace B h V x z E bP W A' U f
  let X:= install B ξ (wired 1 ξ B U)
  have he:= aperture_taylor x z E W Q X (le_trans y A'.door); have hx:= aperture_cost x z E Q X X
  rw [g0]; refine le_trans (by let D:=doll k (increment 1 X); have hp:= norm_add_le (D - TX X X) (TX X X); rw [sub_add_cancel] at hp; exact hp) (?_ : ‖doll k (increment 1 X) - TX X X‖+ ‖TX X X‖ ≤ _)
  refine add_le_add (le_trans he ?_) ((by rw [pow_two]; exact hx : ‖TX X X‖ ≤ (2:ℝ)⁻¹*ℓ*‖X‖^2).trans ?_) <;> gcongr

-- final Broom-birth estimate: unlike path-global projector expense
-- this makes the approximation on WellDrawn at both tiny and ordinary lease.
def lapAsset (x:Site N) (k B:ℕ)(h: 2*(B+1)< (More N).val)(E:Pattern P T r d a v)(q:FrameA B):ℂ:=
    taxpayer x E (k:=k) ((install B (node x) ∘L collectF B (node x) h) q) ((install B (node x) ∘L collectF B (node x) h) q)
lemma paint_it {α:ℝ}(hα:0≤α)(f:pingS Τ S U) (s:Tiny (Spindle.patch B ξ) U α): ‖τ U - lapAsset x k B h E (receiveMark B ξ U 1)‖ ≤ broadError ℓ (λp * Τ) (rawError V (λp * Τ) B Τ α):= by
  obtain ⟨fX,hx,fη,hμ⟩:= permit_trace B h V x z E bP W A' U f
  let X:= Φ; let Y:=paintedMark B ξ U 1; let F:=receiveMark B ξ U 1; let c:=ℓ
  let G:=J; let F':=G F; let L:= λp * Τ
  let δ:= 2*group.colorScale*(4*B*α)*Τ; let w:= rawError V L B Τ α
  have hl(i:Turn B):= receive_cost B ξ h U fX s hα (x:=i)
  have hp:=p.threshold_pos; have hw:=group.colorScale_pos; have hD:=V.positive
  have hδ: 0≤ δ:=by unfold δ; positivity
  have hY:‖Y-F‖≤δ:= (pi_norm_le_iff_of_nonneg hδ).mpr fun i=>(hl i).1
  have ht: ‖F‖≤ Τ:=(pi_norm_le_iff_of_nonneg hp.le).mpr fun i=>(hl i).2.2
  have hF (y:FrameA B){v:ℝ}(p:‖y‖≤v): ‖G y‖≤ λp * v:= (install_price ..).trans ((collect_price B ξ h y).trans (mul_le_mul_of_nonneg_left p (by positivity)))
  have hf : ‖F'‖ ≤ L:= hF _ ht
  have hK : ‖X-F'‖ ≤ w:= by
    have hc := hF _ hY; rw [map_sub] at hc
    exact (norm_sub_le_norm_sub_add_norm_sub X (G Y) F').trans (add_le_add hμ hc)
  have ha:0≤ℓ:= stencil_cost z E x Q
  have hu: ‖TX X X-TX F' F'‖≤ (2:ℝ)⁻¹*ℓ*w*(2*L+L):= by
    have hr:TX X X-TX F' F'= TX (X-F') X+ TX F' (X-F'):=by simp only [map_sub,_root_.sub_apply]; abel
    rw [hr]; apply (norm_add_le ..).trans; rw [mul_add]
    have ho(U V:A)(u v:ℝ)(hu:‖U‖≤u)(hv:‖V‖≤v): ‖TX U V‖ ≤ (2:ℝ)⁻¹*ℓ*(u*v):=(aperture_cost x z E Q U V).trans (by have hg:=(norm_nonneg _).trans hu; gcongr)
    exact add_le_add ((ho (X-F') X w (2*L) hK hx).trans_eq (by ring)) ((ho F' (X-F') L w hf hK).trans_eq (by ring))
  rw [fη]; apply (norm_sub_le_norm_sub_add_norm_sub _ (TX X X) _).trans; refine add_le_add ((aperture_taylor x z E W Q X (le_trans hx A'.door)).trans ?_) hu
  gcongr
#print axioms inBasket
#print axioms paint_it
end YM.CF.LitCurrent.Surplus
