import YM.CF.Stilo.Hype
import YM.CF.Scion.Train
set_option quotPrecheck false
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Scion
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Scree Pastry Stilo Urn Palot Hake
variable {ι A n M: Type*}[LinearOrder n][Fintype n][LinearOrder M][Fintype M]

set_option maxHeartbeats 500000
open Pec Proa Hest Hive Spire Skye Levier Cascade Kennel
variable {L N Q B:Side}{j:ℕ}{o:Odd L.val}{e d:ℝ}{Y:Pricing j L o (Thread j)}(P:Grasp Y B e)(m:Male)
variable (G:Ratio (mid N B) (mid Q B))(H:Aim (mid Q B))(J:Aim (mid N B))(x:Rent0 G e)(U:Pane (mid Q B))(ψ:cro G d)(ATO: ψ.val=(unionP x.val,Tulip.profile U))(ho:Odd G.count.val)(O: Meter TailB G d)(V: Meter Grave G d)
-- single authentic Path valuation fertility
variable {K':Type*}(S:WG K')(R:K'→Male)(I:K')(W:R I=m)(t:S I (mid Q B) (Tulip.profile x.val.1)=H.den x.val.1)
variable (wk:IsStarProjection (spar j m U))(we:IsStarProjection (spar j m x.val.1))(wr:IsStarProjection (spar j (upMale L o m) x.val.2))(wd: chillF G d ψ=ψ)
def postH(Λ: Finset (Branch.Seal (Site (More (mid Q B))))): Weave (Iota G) (Single (mid N B)):=⟨mount (LenT G d O ψ Λ), Urn.soar (KinG G d V ψ Λ), kins G ho d V ψ Λ wd⟩
variable (g:fulfills G ho d (j:=j) R S I O V ψ)(p:0<e)(hv:G.count=L)(u:P.roundZ≤ ((mid N B)).val)(hk:‖coatG L o j G m H.den x.val‖<1) -- tune order

include we
lemma kennelU: cartsL (switchG G).symm (nest P H m x.val.1)=acts (exp (dg (capT (foal j true m G (unionP x.val)) (foot G (H.den x.val.1))))) (graft G P x.val.1 m):=by
 let he:=we; let f:=spar j m x.val.1; let C':=capT f (H.den x.val.1)
 have h':= Hive.relabelExp (switchG G) C' (tag_g (H.den x.val.1) he).nil (changeM P x.val.1 m); change cartsL _ (acts (exp (dg C')) _) = _; rw [h']; have hx: portW ((switchG G).symm) C'=capT (foal j true m G (unionP x.val)) (foot G (H.den x.val.1)):=by change foot G ((1-f) * (H.den x.val.1)*f)=_; rw [foot_mul, foot_mul,foot_sub,foot_one]; rfl -- tune
 rw [hx]; rfl

omit we
include ATO t W g wd
lemma seatsC : let Q':= Urn.stick (foot G (spar j m U)); let W₀:=postH G ψ ho O V wd univ; let B':=wh j G.count ho true m G (unionP x.val); let V':= ticketT (Thread j) true m G (unionP x.val); let U':=ticketT (Thread j) false m G (unionP x.val); let T':=traitP B' (pine j G.count ho (Thread j) true m G (unionP x.val)) V' (capT (foal j true m G (unionP x.val)) (foot G (H.den x.val.1)))
 W₀.pals=fuelC Q' B' T' V' U' ∧ W₀.seats= fun i (x:LeanV (Single (mid N B)))=> if x.1= !(Q'.seek i) then enC Q' B' T' V' U' i (patchQ G x.2) else 0:=by
 subst m; intro Q' W₀ B' V' U' T'; let Z':=prism G.count ho j S R I G (unionP x.val); have hz:Z'=T':=by unfold Z' T' prism Proa.prime; unfold unionP; rw [t]; rfl
 have he:(KinG G d V ψ univ)=(oakN G fun i=>mineC G ho d (j:=j) R S I i ψ):=funext fun a=> funext fun b=>funext fun c=>funext fun z=>g.2 a b c z
 have hl: LenT G d O ψ univ= Radix G (fun i=> mineB G ho d (j:=j) R S I i ψ):=by unfold LenT; congr 1; funext i; exact g.1 i
 let F:= postH G ψ ho O V wd univ; have hx: F.pals=fuelC Q' B' T' V' U':=by change Urn.soar (KinG G d V ψ univ)=_; rw [he,←hz]; exact prime_F G ho d R S I _ _ ψ ATO
 have hQ:F.seats= fun i (x:LeanV (Single (mid N B)))=> if x.1= !(Q'.seek i) then enC Q' B' T' V' U' i (patchQ G x.2) else 0:=by
    change mount (LenT G d O ψ univ)=_; rw [hl]; funext i x'; rw [show (!(Q'.seek i))=(twigS i).1 from Bool.not_not _,←hz]; exact prime_A G ho d R S I _ _ ψ ATO i x'
 exact ⟨hx,hQ⟩
end YM.CF.Scion
