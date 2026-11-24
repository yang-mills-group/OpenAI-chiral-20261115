import YM.CF.BPress.Mount.Vases
/- pointwise restoring uncancelled terms. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Mount
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Spin SpinSign Spin.Pledge Cube Lat SU Spin.Paint Nacre Laic Font Tulip Tenant Dial Scroll Thera Meadow Topology Habitat Habitat.Upled Habitat.Plain Engine Nougat Pf Primary
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Classical YM.CF.BPress.Vesper YM.CF.BPress.Habitat YM.CF.BPress.Habitat.Plain YM.CF.BPress.Habitat.Driver
attribute [local instance] opCStarAlgebra
open Driver Currency RealBook Actor Ledger Spark Vesper Shale Fare Machine Shot Till Store Skye Girt Scree Voice Noon Phase Extensor Stamps Grid Hazel Net Locale Push.AbsoluteSums --
variable {s m B N:Side} {D:BandWidth} {T: Sheet.Atlas}{X Y Z W:Pledge}{a:ℕ}{c d L y u v μ q ε:ℝ}{R:Driver (mid m B)}{P: Edition R}{G:Brace.Duet m B}{U:GramM (mid m B)}{p:Wish R X Y Z}
variable {K:Type}{g:K→R.Pose} (A:Bands (More (mid m B)) D)(F:Net (More (mid m B)) T L y c d a) (h:Tiling (More (mid m B))) (C:Calyx P g) (r:ℕ)
local notation "A0"=> Theatre (mid m B)
open Awards Silhouette
variable {i:A.Index}
local notation "Λ"=> (mid m B)
variable {I:Type} [Fintype I][DecidableEq I] (E:I→Support (More (mid m B)))
def dues(T:I→ℂ)(i:A.Index):=∑ j:I with abyss A i r (E j), T j
abbrev δRest(T:I→ℂ)(i:I):= if currencyT A r (E i) then T i else 0
lemma budget_choice (T:I→ℂ) : ∑ i:A.Index, dues A r E T i=(∑ i,T i)-(∑ i,δRest A r E T i):=by
 have he:= Abyss.sum A r E T; unfold dues δRest; simp_rw [←sum_filter]; exact eq_sub_of_add_eq he.symm -- tune
-- note argument ordering, unused g
variable (s:List A.Index) (u':A.Slates)(x:Orbit (mid m B))(w:K) (z:Shot (mid m B))
abbrev notary (i:A.Index) := CO A F h C r i (clueT (T:=T) (y:=y) A x u' i)
lemma mint_mark (t:s.Nodup)(v:∀ i,i∈s):readout (T:=T) (y:=y) A s (candid A F h C r) u' x.1= Complex.exp (-(∑ i:A.Index, notary A F h C r u' x i)) • readout (T:=T) (y:=y) A s (fun i=> Chalk.pairTest A i F h) u' x.1:=by
 unfold readout candid; rw [walk_scalar,walk_prod s t v, ←Complex.exp_sum,sum_neg_distrib] -- tune scalar
abbrev ΔRest (P: Edition R)(b:R.Pose)(z:Shot Λ) := (∑ i:Tenor (More Λ),δRest A r scaffold (fun i=>P.op i b) i)+(∑ i:Support (More Λ),δRest A r id (fun i=> P.logG i b z) i)
structure Seeing (A:Bands (More (mid m B)) D)(F:Net (More (mid m B)) T L y c d a)(h:Tiling (More (mid m B)))(r:ℕ)(u':A.Slates)(b:R.Pose)(x:Orbit (mid m B)):Prop where
 eq(i:A.Index): Along (deep A i r) (readingX A F h i (clueT (T:=T) (y:=y) A x u' i)) b.val
variable (J:Passports R U G p P W q ε u μ v)
include J
structure Held (P:Edition R) (U:GramM (mid m B))(A:Bands (More (mid m B)) D) (r:ℕ)(u:Orbit (mid m B))(z: Shot (mid m B)): Prop where -- notation Λ from local binder got weird
 field:z.field=u
 γB :∀ (i:A.Index) (t:Support (More (mid m B))), t⊆ deep A i r → barren U z t
-- sum identity dot
lemma dot (Q:Seeing A F h r u' (g w) x)(K:Held P U A r x z) : (-∑ i:A.Index,notary A F h C r u' x i) + (stark (g w)-Pec.pigment U.J.I (g w).val.G-Spire.zen (Spire.hum m B G (g w).val.G (g w).val.X))+ (∑ i, P.logG i (g w) z) = ΔRest A r P (g w) z :=by -- tune arg order
 let u:= fun i=>P.op i (g w); let l:=fun i=>P.logG i (g w) z; have he(i:A.Index):notary A F h C r u' x i= dues A r scaffold u i + dues A r id l i:= by
    let w':= g w; let X(i):= readingX A F h i (clueT (T:=T) (y:=y) A x u' i); have q(i):=Q.eq i; rw [notary,CO,ledgerTerm]; apply congrArg₂ (·+·)
    · exact sum_congr rfl (fun j b=> ((C.pay _).local0 (X i) w'.val ((q i).drop ((mem_filter.mp b).2.2))).trans (C.eye w j))
    apply sum_congr rfl; intro b h'; let t:abyss A i r b:= (mem_filter.mp h').2; have k:(readingX A F h i _).1=x.1:= (rfl:(X i).1=x.1); have hv:= C.C_eye w b; have ht:Along b (X i) w'.val:=(q i).drop t.2; change C.hull b (X i)=P.logG b w' z; rw [(C.phaseRec b).local0 (X i) w'.val ht,J.bare b z w' (K.γB i b t.2)]; apply hv.trans; exact J.reads _ _ _ _ _ (Along.refl ..) ((K.field.symm ▸ (ht.symm).up)) -- tune K.field ▸ k
 rw [←J.issuer]; simp_rw [he,sum_add_distrib]; rw [budget_choice,budget_choice]; unfold ΔRest u l; ring -- tune methods
end YM.CF.BPress.Mount
