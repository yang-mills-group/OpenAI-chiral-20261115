import WakeRoad.Margosa
/-! # Oriented comparisons and deck legality. -/
set_option autoImplicit false
set_option maxHeartbeats 240000
set_option synthInstance.maxSize 25000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation.Yoke
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Tenant Tap Tulip Branch Fir Scree Buffered Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Skye Precision Tree Fock
attribute [local instance] opCStarAlgebra
open PhysicalNext.JointLoad.Heir
open YM.WakeRoad CF.Pannier.Chancel Rous Pressure Papal EmberWind Work.E08
open Gleam Regis Regis.Head Gleam.Wake
open CF.Gingham.Ruff
local notation "G₅"=> SU.group
-- holdings orientation = id or Signed.mirror3. support geometry anchored lifted on grid.
namespace ArborJet
variable {N:Side}
local notation "M"=> Signed.mirror (3:Axis)
local notation "Z" w:max=> Lattice.wrap (More N) (2 • ((w:ℤ) • Lattice.step (3:Axis)))
local notation "T" w:max=> affine (Signed.mirror (3:Axis)) (Z w)
local notation "t*"=> (3:Axis)
-- reflected oriented plaquettes, cost on wrong offset and unit route
abbrev frigid(a:PlaqAxes):ℤ:= if a.val.2=t* then -1 else 1
abbrev distal (a:PlaqAxes):Cover:= if a.val.2=t* then -Lattice.step t* else 0
abbrev town (w:ℤ)(y:Seat N)(a:PlaqAxes):Seat N:= (T w) y+wrap (More N) (distal a)
-- exact conjugated oriented test. establish before cost vs signs
lemma planeFace (U:Pane N)(w:ℤ)(y:Seat N)(v:PlaqAxes) :
 let _γ:=v.val.1; let μ:=v.val.2; let x:=town w y v
 let A:=faceValue U (x,v)
 let k:=U (x,t*)
 faceValue (Lattice.pull M (Z w) U) (y,v)= if μ=t* then k⁻¹ * A⁻¹ * k else A :=by
 intro γ μ x A k; obtain ⟨⟨a,b⟩,h⟩:= v; have hx: b≤ t*:=by apply Fin.le_last
 have hz:a≠t*:= (lt_of_lt_of_le h hx).ne
 dsimp only [μ]; split
 · next q=>
   subst b; let y':Seat N:=(T w) y; have h0:x=y'-Lattice.step t*:=by unfold x town distal; dsimp only; rw [if_pos rfl,map_neg,wrap_step,sub_eq_add_neg]
   unfold faceValue; rw [travel_pull]; unfold A k; rw [h0]; unfold faceValue
   simp only [square,List.map_cons,List.map_nil, posDir,negDir, Step.rotate,Signed.mirror]
   simp only [Equiv.refl_apply,Ne.symm hz,decide_false,Bool.xor_false,decide_true,Bool.xor_true] -- check flip index
   change travel U y' ([posDir a,negDir t*,negDir a,posDir t*])= _ -- square'?
   change travel U y' [posDir a,negDir t*,negDir a,posDir t*]= (U (y'-step t*,t*))⁻¹ * (travel U (y'-step t*) (square a t*))⁻¹ * U (y'-step t*,t*)
   simp only [square,travel,Step.neg_read,Step.pos_read,Step.vec_neg,Step.vec_pos,mul_one]
   rw [show y'+step a+ -step t* - step a=y'-step t* by abel,show y'+step a+ -step t* + -step a=y'-step t* by abel,show y'-step t*+step a+step t* - step a=y' by abel,show y'-step t*+step a+step t*+ -step a - step t* = y'-step t* by abel,show y'+step a-step t* = y'-step t* + step a by abel]
   group
 next v=>
 change faceValue (Lattice.pull M (Z w) U) (y,⟨(a,b),h⟩)=_
 unfold faceValue; rw [travel_pull]; unfold A x town faceValue distal; rw [if_neg v,map_zero,add_zero]; congr 1
 simp [Step.rotate,Signed.mirror,square,posDir,negDir,Ne.symm hz,Ne.symm v]

-- ship clearance, universal ≤ radius c needed.
private theorem billHeld : ∃ i:ℕ,∀ a:PlaqAxes,∀ r:Signed,(skewSlot SU.group (keelSlot a) r).length ≤ i:= by
 have h(a:PlaqAxes)(r:Signed):∀ᶠ k:ℕ in atTop, (skewSlot SU.group (keelSlot a) r).length≤ k:=eventually_ge_atTop _
 exact (eventually_all.mpr (fun a=> eventually_all.mpr (h a))).exists
abbrev debt:ℕ:=billHeld.choose
lemma commutes (a b:Seat N)(w:ℤ) :separation ((T w) a) ((T w) b)= separation a b:= by simp only [affine,separation_translate,separation_signed]
lemma turf (w:ℤ) : (T w) (0:Seat N)= Z w:=by unfold affine; rw [Signed.act_zero,zero_add]
lemma wood {I:Type}[Fintype I](V: Gleam.Wake.Vessel SU.group (More N) I){d:ℕ}{S: Support (More N)}(v:debt≤d)(t:∀ i: I,BlockP (debt+4) (V.origin i) ⊆ S):V.Ship S d:=by
 have he(i:I)(s:Signed): (V.crew i s).length≤debt:= billHeld.choose_spec _ _
 refine ⟨fun i x p=>?_ ,fun i j b=>?_ ,fun i j=>(he i j).trans v⟩
 · apply t i; apply blocks_test.mpr; exact (Work.E01.sep_touched _ _ p).trans (by omega)
 let X:=affine j b; let f:=(V.viewFace i j b).1
 obtain ⟨l,hl⟩:=(show Surjective X from (Push.Local.turnSites j b).surjective) f
 apply mem_image.mpr; refine ⟨l,t i (blocks_test.mpr ?_),hl⟩
 have hc:separation (X (V.origin i)) f ≤ debt:=(Work.E04.slot_separation (V.crew i j) (X (V.origin i))).trans (he i j)
 rw [←hl] at hc; exact (show separation (V.origin i) l ≤ debt from (by simpa only [X,affine,separation_translate,separation_signed] using hc)).trans (by omega)

-- flag false on positive Armada
local notation "Q"=> SU.group.ColorIndex
variable (m:ℕ)(w:ℤ)(b:Bool)
abbrev anis (i:Postcard m):PlaqAxes:=i.1.2
abbrev birthplace (i:Postcard m) : Seat N:=wrap (More N) i.1.1.val
abbrev taking (i:Postcard m) : Seat N:= if b then town w (birthplace m i) (anis m i) else birthplace m i
abbrev elector: Vessel SU.group (More N) (Postcard m):= ⟨fun i=> ((taking m w b i,anis m i),i.2)⟩
abbrev homebase:Seat N:= if b then Z w else 0
lemma estate (i:Postcard m): separation (homebase (N:=N) w b) (taking m w b i) ≤ m+1:=by
 let x:=birthplace m i (N:=N)
 have hx:separation (0:Seat N) x ≤ m:=by simpa [x,birthplace] using (separation_box_add (0:Seat N) i.1.1.property)
 cases b
 · exact hx.trans (by omega)
 let Y:= town w x (anis m i)
 change separation _ Y ≤ _
 have t:separation ((T w) x) Y ≤1:=by
   unfold Y town distal; split; swap; · simp
   rw [map_neg,wrap_step,separation_comm,separation,add_comm,add_sub_cancel_right,pdist_neg]; exact Lattice.pdist_step _
 have H := (commutes (N:=N) 0 x w).le.trans hx; rw [turf] at H
 exact (separation_triangle (Z w) ((T w) x) Y).trans (Nat.add_le_add H t)

#print axioms planeFace
