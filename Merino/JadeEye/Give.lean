import Merino.Brooch.Strand

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.JadeEye
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Swell

open Dial BProof Brooch
open TreasuryFog Paige Vault
attribute [local instance] loreM loreN
open Roots

variable {n:Side}

-- Unscaled offer
structure Exhibit (P:BudgetPoint)(o:Site n)(F:Pane n→ℂ)(a:ℝ) : Prop where
 price: 0≤a
 fog: Measurable F
 room: LocalOn (sleeve P o) F
 gage(u:Pane n)(g:Seat n → SU.E): F (Lattice.gauge g u) = F u
 brings(Y:Aura n)(y:sleeve P o⊆ Y.val)(D Z:Support (More n))
   (V:Orbit n)(p:V.1∈σX P Y D): Pence P.order (fun x=> F (pressQ P Z V.1 x)) 0 a

abbrev fume (F:Pane n→ℂ): Firing n:=fun v=> F v.1 • 1
variable {P:BudgetPoint}{h a:ℝ}{q:ℕ}{o:Site n}{F:Pane n→ℂ}

lemma sample (f:Exhibit P o F a) {T:Aura n}(t:sleeve P o⊆T.val):Herb P q T h (fume F) a:=by
 refine ⟨f.price,?_,fun _ _ _ _ _=>rfl⟩
 intro X k D _ _
 have v:= t.trans k
 have e:= AuraOp.sat (P:=P) (X:=X) (D:=D) h (fun z=>F z.1) (1:FC (Dwell n))
    (Ark.one h) f.price (fun V u Z _=>f.brings X v D Z V u)
 rw [mul_one] at e
 refine ⟨⟨?_,fun _=>Sector.one.scale _,fun i j _ _ e _=> congrArg (· • (1:FC (Dwell n))) (f.room i.1 j.1 (agrees_mono e v)),?_⟩,e.pay⟩
 · exact ((show Continuous (fun x:ℂ=>x • (1:FC (Dwell n))) by fun_prop).measurable.comp (f.fog.comp measurable_fst))
 intro i t' _
 change F (Lattice.gauge t' i.1) • _=sauce _ _ _ (F i.1 • _)
 rw [f.gage,sauce,singT,win_c,win_i,twist_scalar,map_one];rfl


def icost:ℝ:=Real.exp (10* (9:ℝ)^4)
lemma icos_pos:0 < icost:=Real.exp_pos _

variable {G B L:Side}{j:ℕ}{jY:Odd L.val}{Yk:Pricing j L jY (Thread j)}{d:ℝ}
variable {U:Grasp Yk B d}{R:GramM (mid G B)}{K:Scree.Loom (mid G B)}
local notation "N"=>mid G B
variable {c:ℝ}

lemma gives {o:Site (mid G B)} {F: Pane (mid G B) → ℂ}{X : Obs (mid G B)}(f:Exhibit R.p o F a) (z:ℂ)
    (v:Allowed (sleeve R.p o) X)
    (s:∀V:Pane (mid G B),X V=z • F V • 1)
    (g: ‖z‖*(a*icost)≤c):
   ∃ V T, Office U R K q h c c o X V T:=by
 let x:=sleeve R.p o
 have ht: {node o}⊆x:=halo_subset _ _
 let I:Aura N:= ⟨x,⟨node o,ht (mem_singleton_self _)⟩⟩
 let H:=Corolla.eighth R.p.B
 let W:Aura N→Firing N:=fun i=> if i=I then fume F else 0
 have b:Barrage R.p q {node o} h W H (a*Sour.tact H R.p.B I) (a*Sour.tact H R.p.B I):=
   Barrage.single _ _ (Flight.once (sample f (le_refl x))) ht
 have t : Sour.tact H R.p.B I ≤ icost:=by
    unfold Sour.tact icost
    apply Real.exp_le_exp.mpr


    have hb : 1≤ (R.p.B:ℝ):=by exact_mod_cast R.p.B_pos
    have e: H≤10:=by
       have:=div_le_self (a:=(8:ℝ)) (by norm_num) hb
       unfold H Corolla.eighth; linarith only [this]
    refine mul_le_mul e ?_ (by unfold widthK; positivity) (by norm_num)
    exact_mod_cast Corona.tile (node o) 4 R.p.B R.p.B_pos
 have hp : ‖z‖*(a*Sour.tact H R.p.B I)≤c:=by
     apply le_trans _ g; gcongr; exact f.price
 refine ⟨fun j=> X j.1,z • W,v,(b.swell z).bigR hp hp,?_,fun j _=>v.modes_use _,fun j _=>rfl⟩
 intro D proj u
 have he:(∑i:Aura N, (z • W) i D) = z • F D.1 • 1:=by
   simp [Pi.smul_apply,W,fume,apply_ite (fun t:Firing N=> t D),smul_ite]
 rw [he, act_smul,act_smul,act_one]
 rw [s,act_smul,act_smul,act_one,map_smul,map_smul]
