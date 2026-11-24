import YM.SU5.Aria.Drape
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 75000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
variable (P: Spine) (j:Axis) (x:P.Spectrum0 j)
open Aria Set TopologicalSpace Metric
local notation "Λ"=> P.par
local notation "κ"=> P.calibration
local notation "ℓ"=> (κ).ℓ
local notation "R"=> ruler P.par.block
local notation "Μ"=> timeMesh P.par
local notation "N"=> notch (timeMesh P.par)
local notation "Γ"=> marks (timeMesh P.par)
local notation "H"=> P.large
local notation "Y₀"=> P.run
local notation "Φ" => P.colorSpace j x
local notation "X"=> P.ColorHil j x
variable (n w:ℕ)(D:P.Apron)(L:List Axis)
abbrev vtile (r:Cover) : P.VMark:=fun i=> notch (timeMesh P.par) n (r i)
def cruise (r:Cover): P.Test→ₐ[ℂ]P.Test:= L.foldr (fun i (a:P.Test→ₐ[ℂ]P.Test)=> (P.shifts i (r i)).comp a) (AlgHom.id ℂ _)
local notation "S" i:max=>P.shifts i
lemma cruise_step (v:Cover) : P.cruise (j::L) v= ((S j) (v j)).comp (P.cruise L v):= rfl
lemma followsChart (v:Cover)(f:P.Test): (P.cruise L v f).val=Vacancy.cad κ L v f.val:=by induction L with | nil=> rfl | cons i l ih=> change relocate κ i _ (P.cruise l v f).val=relocate κ i _ _; rw [ih]; rfl
lemma cruise_color (v:Cover){f:P.Test}(p:f∈enclave κ): P.cruise L v f∈ enclave κ:=by induction L with | nil=> exact p | cons i l ih=> rw [P.cruise_step,AlgHom.comp_apply]; exact P.shifts_keep i (v i) ih
abbrev chartAll (v:Cover) := P.cruise Vacancy.ordinate v
lemma chart_transverse (v:Cover)(f:P.Test) : P.chartAll v f = P.shifts j (v j) (P.cruise (Vacancy.spare j (look j)) v f):= by
  have he : ((P.chartAll v) f).val= (Vacancy.chart P.calibration v) f.val:= P.followsChart ..
  apply Subtype.ext; rw [he,Vacancy.chart_piece κ j v ((marque ..).1 f.property), P.shifted,P.followsChart] -- name
lemma cruise_mesh (p:ℤ)(r:Cover)(f:P.Test): P.cruise L r ((S j) p f)= P.shifts j p (P.cruise L r f):= by induction L with
 | nil=> rfl
 | cons i l h=> simp only [cruise_step,AlgHom.comp_apply,h,P.march j i _ _ _|>.symm] -- simp P.march syntax
lemma chart_ids (f:P.Test)(a p:Cover) : P.chartAll p (P.chartAll a f)=P.chartAll (p+a) f:= by
 unfold chartAll; apply Subtype.ext; simp only [P.followsChart,Vacancy.cad_plus _ _ ((marque ..).1 f.property)] -- p named
lemma cruise_raise (p:Cover)(z:ℕ)(f:P.Test): P.conveying n (z-n) (P.cruise L p f)= P.cruise L (castor Μ n z ∘ p) (P.conveying n (z-n) f):=by induction L with
 | nil=>rfl
 | cons i l ih=> rw [P.cruise_step, AlgHom.comp_apply,P.walk_rig, ih, P.cruise_step,AlgHom.comp_apply]; rfl
lemma cruise_id (v:Cover) {f:P.Test}{z:Cover} (h:∀i∈ L,v i=z i) : P.cruise L v f=P.cruise L z f:=by induction L with
 | nil=>rfl
 | cons i l ih=>rw [P.cruise_step,P.cruise_step,AlgHom.comp_apply,AlgHom.comp_apply,h i (List.Mem.head ..),ih (fun j h'=>h j (List.Mem.tail _ h'))]

section acting
open SlabMark Vacancy
variable (p:0<w)
local notation "ϕ" u:max=>P.voxTest j n u
local notation "U" a:max=>((P.voyageF j x).crew a).play
private lemma equality_handy (L:Hilbert)(X₀:Type*)[CStarAlgebra X₀] (R': X₀→⋆ₐ[ℂ] L.Op)(A B Y:X₀)(h:A*B=Y*A) (U₀:L.Op) (p:U₀= R' A): U₀.comp (R' B)=(R' Y).comp U₀:=by
 subst U₀; change R' A*R' B=R' Y*R' A; rw [←map_mul,←map_mul,h]
lemma performs_equality (A B Y:P.Physical j)(h:A*B=Y*A) (U₀:(P.ColorHil j x).Op) (p:U₀=Φ A): U₀.comp (Φ B)=(Φ Y).comp U₀:=
 equality_handy (P.ColorHil j x) (P.Physical j) (P.colorSpace j x) A B Y h U₀ p
private lemma handy_twice (E:Hilbert)(A B K X' W:E.Op)(u:K.comp A=B.comp K) (v:X'.comp B=W.comp X'):(X'.comp K).comp A=W.comp (X'.comp K):=by
 change X'.comp (K.comp A)=_; rw [u, ← Alliance.just («H»:=E),v]; rfl
private lemma handy_release (E:Hilbert)(A B C T K:E.Op)(p:A=B)(g:T.comp B=C.comp T)(u:T.comp K=ContinuousLinearMap.id ℂ E.space) : T.comp (A.comp K)=C:=by rw [p, ← Alliance.just («H»:=E),g, Alliance.just («H»:=E),u]; rfl
lemma released_truck (y:P.VMark)(A B C:(P.ColorHil j x).Op)(e:A=B)(u:(P.truck j x y).comp B=C.comp (P.truck j x y)): P.charter j x y A=C:=by
 apply handy_release (P.ColorHil j x) A B C _ _ e u; rw [← P.truck_paves,add_neg_cancel,P.truck_zero]
include p
lemma door_move (i:Trans j)(t:ℤ) (f:P.Card j n w)(u:ϕ f.val∈enclave κ):∃ (v:P.Card j n w)(e:ϕ v.val∈ enclave κ), ϕ v.val= P.shifts (i:Axis) t (ϕ f.val) ∧ ((U i) (N n t)).comp (Φ (P.door j n w p f u))=(Φ (P.door j n w p v e)).comp ((U i) (N n t)):=by
 let y:=alongS Y₀ H n j false w f i t; have hv:ϕ y.val=P.shifts (i:Axis) t (ϕ f.val):= rfl
 have a:ϕ y.val∈enclave κ:= hv ▸ P.shifts_keep i.val t u
 refine ⟨y,a,hv,?_⟩
 exact P.performs_equality j x (P.walksColor j (n,t,i)) _ _ (Subtype.ext (Subtype.ext (shape_across Y₀ H P.law n P.history P.projection.clipped j false (P.room j) w f p i t))) _ (P.meets j x i n t)
local notation "η" t:max => (P.voyageF j x).raw t
local notation "vA" r:max=> (fun i:Trans j=> N n (r (i:Axis)))
set_option maxHeartbeats 600000 in
lemma door_move_list (s:List (Trans j))(r:Cover)(f:P.Card j n w)(u:ϕ f.val∈enclave κ):∃ (y:P.Card j n w)(e:ϕ y.val∈ enclave κ),ϕ y.val= P.cruise (spare j s) r (ϕ f.val) ∧ ((η s) (vA r)).comp (Φ (P.door j n w p f u))=(Φ (P.door j n w p y e)).comp ((η s) (vA r)):=by
 induction s with
 | nil=> exact ⟨f,u,rfl,rfl⟩
 | cons i s ih=>
   obtain ⟨y,e,t,H'⟩:=ih; obtain ⟨v,F,E,Q⟩:= P.door_move j x n w p i (r i.val) y e
   refine ⟨v,F,?_ ,?_⟩; · rw [E,t]; rfl
   exact handy_twice (P.ColorHil j x) _ _ _ _ _ H' Q
end acting
namespace Apron
variable (q:n≥ D.s)(p:Cover)
local notation "uₓ"=> D.zoom P n j
local notation "Uₓ"=> D.zoom P n j + D.zoom P n j
include q
set_option maxHeartbeats 500000 in
theorem transported : ∃ (f:P.Card j n (zoom P D n j+zoom P D n j))(h:P.voxTest j n f.val∈ enclave κ),
 P.voxTest j n f.val=P.shifts j ((uₓ:ℤ)-p j) (P.chartAll p (D.full P n))∧ P.charter j x (P.vtile n p) (D.engine P j x)= P.colorSpace j x (P.door j n (Uₓ) (add_pos (D.zoomP P j n) (D.zoomP P j n)) f h):=by
 let z:= uₓ; let T:=D.engine P j x; let W:= P.ColorHil j x; let V:=P.charter j x; let t:= P.vtile n p; let k:=P.truck j x; let F:=D.full P n
 have hv:0<Uₓ:=add_pos (D.zoomP P j n) (D.zoomP P j n)
 obtain ⟨g,a,e⟩:= D.full_realizes P j n q; have ha:P.voxTest j n g.val∈ enclave κ:=a ▸ P.shifts_keep j z (D.fullColor P n)
 let G':= Φ (P.door j n (Uₓ) hv g ha)
 have hT:T=G':= congrArg (fun u:P.Physical j=> Φ u) (Subtype.ext (a1:=P.door j D.s _ (add_pos (D.pos j) (D.pos j)) (D.cardB P j) (D.color P j)) (a2:=P.door j n (Uₓ) hv g ha) e)
 obtain ⟨f,h,hq,hp⟩:=P.door_move_list j x n (Uₓ) hv (look j) p g ha
 refine ⟨f,h,?_ ,?_⟩
 · rw [hq,a,P.cruise_mesh,P.chart_transverse,P.shifts_sum,sub_add_cancel]
 let E:=P.colorSpace j x (P.door j n (Uₓ) hv f h); have hp' : (k t).comp G'=E.comp (k t):= hp
 exact P.released_truck j x t T G' E hT hp'
end Apron
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.Apron.transported
