import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Locations
import YM.Work.H03
import Gingham.Ruff.Ferry
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Gingham.Ruff
open Function NormedSpace Finset Fock Scree Pastry
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Lattice Wilson Laurent Cube SU Lat Spire Scroll Peaks Drapes Rush Precision Tulip Jet
    Tap Laic Dial Paige Vault Pec Skye Branch
variable {N:Side}

open RG Vow Hake Tenant
set_option linter.unusedSimpArgs false

open Sour Rill
attribute [local instance] Rill.boreKSpace Rill.boreXN Sour.loreM Sour.loreN
open scoped Classical


open MeasureTheory Nacre AnalyticBridge.GaussianFieldAlignment.Locations
def sung (d:Shape): Sweep N:=.mk d.s (wrap N d.t) false
lemma sung_eq (d:Shape)(x:Pane N):
 flashA (sung d) x = Yg d x:= stir_e d false x

variable (d:Shape)(U:UNI SpinIdx)
lemma ping_move_shape (v:ℝ)(S:Support (More N))(x:Pane N):
 pingS v S (Yg d x) ↔ pingS v (sheet d S) x:=by
 let Z:=shiftFaces d.s ((wrap (More N)) (2 • d.t))
 have z(i:Face (Per (More N))):
    SU.group.chord (faceValue (Yg d x) i)=SU.group.chord (faceValue x (Z i)):=
    Face.send_price x i _ _ SU.group.chord SU.group.chord_inv (fun y g=>SU.group.chord_conj g y)
 have k(i):touched (Z i)=sheet d (touched i):= Work.H03.touched_send ..
 constructor
 · intro a i
   obtain ⟨i,rfl⟩:=Z.surjective i
   rw [k, Finset.disjoint_image d.anon_b.1,←z]
   exact a i
 intro a i t; rw [z]
 exact a _ (by rw [k, Finset.disjoint_image d.anon_b.1];exact t)

lemma sheet_hoop (b:ℕ)(y:Site N):
 sheet d (hoop y b)=hoop (finale d y) b:=by
 ext j
 obtain ⟨j,rfl⟩:=d.anon_b.2 j
 have h(k:Seat N): d.anon N k=d.anon N j ↔ k=j:=d.anon_b.1.eq_iff
 simp only [sheet,hoop,Finset.mem_image, halo_spec, mem_singleton,exists_eq_left,
     h,exists_eq_right,bouton_finale]
 simp only [Shape.anon,Lattice.affine,separation_translate,separation_signed]

variable {U':Loom N}{y:Site N}{u:Side}{l r:ℕ}{E q e a c:ℝ}{p:BudgetPoint}
  {A:Fob N e} (g: Briefly p r e U')
  (H:Plastron y u e (a/4) c A)

open MeasureTheory
lemma badgeX (N):∃w:Ids N,Injective (priorP w):= (sepT (n:=N)).exists
def Briefly.dye(x:Orbit N):Dyed N e where
 paneQ := U' x
 live:= g.ceiling.2.paid x
 openZ:=g.pos
lemma Briefly.rollZ (x:Orbit N): g.roll x=(g.dye x).stack:=rfl

lemma pulse_shape (V:Pane N)(w:Ids N)(h:Injective (priorP w))(b:Orbit N)
  (hb:b=(Yg d V,bun (sung d) w)):
 (g.dye (V,w)).actsD d=g.dye b:=by
 have ht:=g.ceiling.2.move V w (sung d) h
 rw [sung_eq,sung_eq] at ht
 subst b
 unfold Briefly.dye Dyed.actsD
 simp only [ht]

include g
lemma coin_spin (V:Pane N)(w:Ids N)(h:Injective (priorP w)):
 coinF g (framed d U H) true (V,w)=
   plinth d U (coinF g H true (Yg d V,bun (sung d) w)):=by
 simp only [coinF,silkcut,retina,liteF,comp_apply,framed_light,g.rollZ,posed_stack,
    ping_move_shape,sheet_hoop,pulse_shape d g V w h _ rfl]
 split
 · rfl
 simp
include H
lemma cologne (G: Tagbill a E u l r p.B)(x b:Orbit N)(h:b.1=Yg d x.1):
 coinF g (framed d U H) true x =
    plinth d U (coinF g H true b):=by
  obtain ⟨w,i⟩:=badgeX N
  rw [(opera g G (framed d U H)).cyl x (x.1,w) (fun _ _ _=>rfl),
      coin_spin d U g H _ w i,
      (opera g G H).cyl _ b (fun j _ _=>show Yg d x.1 j=b.1 j by rw [h])]
#print axioms cologne

