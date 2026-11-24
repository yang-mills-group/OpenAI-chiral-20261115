import YM.CF.Buffered.Quadrat
/-! # Rectangular law evaluates to the donor cube -/
set_option autoImplicit false
set_option synthInstance.maxSize 22000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 420000
noncomputable section
namespace YM.CF.Buffered.Region
open Function Filter NormedSpace SU Lat Lattice Cube Finset Mir Mir.Trip Phase RP MeasureTheory Roost Rails Mil RG WilsonStartup Spark Nova Fock Gloss Scroll Push.SectorMeasure Ordered Cin Stripe Tile
open Installed (point)
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
attribute [local instance] opCStarAlgebra
variable {m v p B:Side}
local notation "N" => CSide v B
local notation "G" => GridM v B
local notation "T" => CSide m B
local notation "I" => Xmind m B
local notation "X" => Pack m B
local notation "W" => Post N
local notation "δ" => Uniform p
local notation "s" => Brace.northZ m B
variable {e x:ℝ} (K: Ticket m v B p e x) (Z:Rail (Uniform p)→Badge v B) (q:Clip) (β u:ℝ)

abbrev Ordered.erect (K:Ordered m v p)(B:Side) : Installed (Rail (Uniform p)) (GridM v B) (Xmind m B):=
 ((Equiv.refl (Rail (Uniform p))).prodCongr (Bays.wall (Post (CSide v B)) Spin).symm).trans ((Equiv.prodAssoc (Rail (Uniform p)) (Post (CSide v B)) Spin).symm.trans (((spirit K B).slots.prodCongr (Equiv.refl Spin)).trans (due _)))
local notation "F" => erect K.K B
local notation "D" v => (Bays.install Spin (v: Post N))
lemma erect_modes (r:Rail δ)(z: W)(j: Spin): point F r ((D z) j)= Mil.side ((K.K.spirit B).zone r z.val) j:=rfl
lemma erect_step (r:Rail δ)(z: W): (D z).trans (point F r)= Mil.side ((K.K.spirit B).zone r z.val):=rfl -- embedding function eq?
namespace Ticket
variable (y:Pack m B)(r:Rail (Uniform p))
local notation "Q" => K.K.fromCube y
lemma erect_sky : Rect.above F = upperP T:=by
 ext i; obtain ⟨⟨r,⟨v',w⟩⟩,rfl⟩:= (erect K.K B).surjective i -- tune
 change point F r ((Bays.install Spin v') w) ∈_ ↔_; rw [show ∀ x,point F r x∈Rect.above F ↔ x∈Tile.sky v B from fun x=> Installed.point_grade ..]; change Bays.install Spin v' w∈_↔ (((K.K.spirit B).zone r v'.val,w)∈upperP T); rw [show Bays.install Spin v' w∈ Tile.sky v B ↔ w∈Mil.above from Installed.point_grade ..]; simp [upperP,Mil.above]
lemma erect_heart (h:y∈secure e x): Heat.seedOp e y = exp (Rect.quiet K F Q):=by
 unfold Heat.seedOp Heat.seedArg; rw [Set.indicator_of_mem (show y∈TallyR m B e 0 from h.1)]; apply congrArg
 rw [cube_R K y h]; unfold Rect.quiet Tile.seed; simp_rw [map_sum]; apply sum_congr rfl; intro v _; exact sum_congr rfl fun j _=> (into_trans _ _ _ (erect_modes K v j) (spin_sector ..)).symm
lemma fence (t:Site T) (i:Axis): seam s t i= if t i= -1 then (-1:ℂ) else 1:=rfl -- K not mentioned
lemma valid_in (i:Axis)(t:Minor N i) :let z:Site T:= (K.K.spirit B).zone r t.val.val
 seam s z i • coupled (side z) (side (z+step i)) i (links y.1 (z,i))= into (point F r) (innerEdge i t (reel r Q)):=by
 intro z; rw [fence,if_neg (fun p=> t.property (((windsAt i (B:=B) K.K r _).1 p).1)),one_smul]; let v':= reach i t; have hz : z+step i=(K.K.spirit B).zone r v'.val:=minor_to (K:=K.K) ..
 rw [hz,walks i (B:=B) K.K r r t.val v' hz y]; exact (Mil.coupled_into _ _ _ _ _ _ (erect_modes K r t.val) (erect_modes K r v') _).symm
lemma strip_sum (i:Axis)(t:Hale N i) : let z:Site T:= (K.K.spirit B).zone r t.val.val; let l:= Region.next i r
 seam s z i • coupled (side z) (side (z+step i)) i (links y.1 (z,i))= chordF r i • coupled ((D t.val).trans (point F r)) ((D (pulse i t)).trans (point F l)) i (outWay i t.val (reel r Q)*inWay i (pulse i t) (reel l Q)):=by
 intro z l; rw [fence]; have hz: z+step i= (K.K.spirit B).zone l (pulse i t).val:=hale_to (K:=K.K) ..; have hp: z i= -1↔ endsAt r i:= (windsAt i (B:=B) K.K r _).trans (and_iff_right t.property)
 rw [hz, walks i (B:=B) K.K r l t.val _ hz y, erect_step K,erect_step K,chordF]; by_cases h: endsAt r i <;> simp [hp,h] <;> rfl
lemma erect_lights : dg (wiel m B s y.1)= Rect.glow F Q:=by
 let P:= K.K.spirit B; let Q':= Q
 let L(t:Site (CSide m B))(i:Axis):= seam s t i • coupled (side t) (side (t+step i)) i (links y.1 (t,i)); let z(r)(i:W):=P.zone r i.val
 have he(t) (i:Axis): ∑ r:W,L (z t r) i=(∑ v:Minor N i, L (z t v.val) i)+∑ v:Hale N i, L (z t v.val) i:=by rw [add_comm]; exact (Fintype.sum_subtype_add_sum_subtype (LastSite i) (f:=fun j=> L (z t j) i)).symm -- tune
 unfold wiel; rw [edge_energy y.1 s]; unfold Rect.glow pit; simp_rw [map_add,map_sum,sum_add_distrib]; rw [←Equiv.sum_comp P.slots (fun i=> into _ rest),Fintype.sum_prod_type, add_assoc]; apply congrArg₂ (·+·); swap
 · change ∑ i:Axis, ∑ p:Site T, L p i= _; rw [←sum_add_distrib]; simp_rw [← Equiv.sum_comp P.slots (fun p:Site T=> L p _),Fintype.sum_prod_type]; rw [sum_comm]; apply sum_congr rfl; intro r _; rw [←sum_add_distrib]; apply sum_congr rfl; intro i _; change ∑ v:W, L (z r v) i= _; rw [he]; apply congrArg₂ (·+·); · exact sum_congr rfl fun a _=> K.valid_in y ..
   unfold Rect.scar Tile.joinF; rw [smul_sum]; exact sum_congr rfl fun a _=> K.strip_sum y ..
 exact sum_congr rfl fun i _=> sum_congr rfl fun j _=> (into_trans _ _ _ (erect_modes K i j) rest_placed).symm

def estate (y:X) := Rect.logo Z F (K.K.fromCube y)
lemma assembled : heatTerm K.pin K.W q β x e u s (K.estate Z) y=Rect.emit K Z q β u F Q :=by
 unfold heatTerm Rect.emit Rect.gold; rw [K.on_weights y q β]; by_cases h:y∈secure e x; swap
 · rw [←on_weights K, veil K y q β h,zero_mul]; by_cases e':y∈TallyR m B e 0 -- tune binder shadow
   · unfold primal; rw [Set.indicator_of_notMem (show y.1∉Calm _ _ _ from fun p=>h ⟨e',p⟩)]; simp
   rw [Set.indicator_of_notMem e',mul_zero]
 unfold Rect.player Heat.scalarWeight estate; have hz:y∈TallyR m B e 0:=h.1; rw [Set.indicator_of_mem hz,Set.indicator_of_mem hz,←Heat.seed_match K.pad hz,←act_mul, bra_fix, K.erect_heart y h,ferment (self_wiel ..) u,erect_lights K,Complex.ofReal_mul, erect_sky K,neg_one_mul]; ring
lemma pressure : heatNum K.pin K.W q β x e u s (K.estate Z)= prism (Uniform p) K Z q β u:=by
 unfold heatNum; rw [into_coast K.K]; rw [show prism δ K Z q β u=Rect.vista K Z q β u F from Rect.stages ..]; apply integral_congr_ae; exact Eventually.of_forall fun i=> (K.assembled ..).trans (by rw [atCube]) -- tune
end Ticket
end YM.CF.Buffered.Region
#print axioms YM.CF.Buffered.Region.Ticket.pressure
