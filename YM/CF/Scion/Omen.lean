import YM.CF.Scion.Xeno
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
variable (g:fulfills G ho d (j:=j) R S I O V ψ)(p:0<e)(hv:G.count=L)(u:P.roundZ≤ ((mid N B)).val)(hk:‖coatG L o j G m H.den x.val‖<1) -- tune order
include t ATO wk we wr wd g u W p hv hk
lemma oZ(Pa:List (LeanV (Single (mid Q B))))(T:List (Oboe (Single (mid Q B)))): TagG (spar j (upMale L o m) x.val.2) (Budget L o H.den J.den G m j x.val) ∧ fire (Thread j) G m (unionP x.val) (cartsL ((switchG G).symm) (acts ((nursery (spar j m U) wk).eval (rollC put Pa) * rollC bell T) (nest P H m x.val.1)))= (Complex.exp (-(lush G P m H.den x.val))) • acts ((nursery (spar j (upMale L o m) x.val.2) wr).eval (issue (portX ((switchG G).symm) (postH G ψ ho O V wd univ)) (rollC put Pa) (rollC bell T))) (acts (exp (dg (partM L j o N B m J.den x.val.2))) (acts (exp (dg (Budget L o H.den J.den G m j x.val))) (changeM P x.val.2 (upMale L o m)))) :=by
 subst L m
 let K':= foot G (spar j (R I) U); let Q':= Urn.stick K'
 have hu:= shone (P:=P) p G rfl u H (R I) x.val x.property (partM G.count j ho N B (R I) J.den x.val.2) Q' ((Scion.cue Pa T).map (tinOre ((switchG G).symm))) wr (tag_g _ wr) hk -- tune
 let V₀:= (unionP x.val); let α:=foal j true (R I) G V₀; let S':=wh j G.count ho true (R I) G V₀; let C:=partM G.count j ho N B (R I) J.den x.val.2; let Z:= capT α (foot G (H.den x.val.1)); let W:=Hest.Budget G.count ho H.den J.den G (R I) j x.val; let P₀:= (spar j (upMale G.count ho (R I)) x.val.2); let A':= (Scion.cue Pa T).map (tinOre ((switchG G).symm)); let Ρq:=graft G P x.val.1 (R I); let γ:= desire G.count j ho G (R I) x.val Z; let T':=postH G ψ ho O V wd univ; let K₀:= ticketT (Thread j) true (R I) G V₀; let K₁:=ticketT (Thread j) false (R I) G V₀; let Φ:=traitP S' (pine j G.count ho (Thread j) true (R I) G V₀) K₀ Z;
 constructor; · exact hu.1
 have hp : (cartsL ((switchG G).symm) (acts ((nursery _ wk).eval (rollC put Pa)*rollC bell T) (nest P H (R I) x.val.1)))=acts (rollC (Proa.dialL Q') A') (acts (exp (dg Z)) Ρq):=by rw [warpGram,kennelU P _ _ H x we]; rfl
 obtain ⟨e',h'⟩:=seatsC (R I) G H x U ψ ATO ho O V S R I rfl t wd g
 let b:=issue (portX (switchG G).symm T') (rollC put Pa) (rollC bell T)
 have hh:b= fixT P₀ Q'.seek (fun i y=>enC Q' S' Φ K₀ K₁ i (patchQ G y)) (fuelC Q' S' Φ K₀ K₁) A':=by unfold b; rw [podT]; unfold T'; rw [e',h']
 rw [hp]; change _= (Complex.exp (-lush G P (R I) H.den x.val)) • acts ((nursery P₀ wr).eval b) (acts (exp (dg C)) (acts (exp (dg W)) (changeM P x.val.2 (upMale G.count ho (R I)))))
 rw [hh, show -lush G P (R I) H.den x.val=altar G P x.val (R I)+invoice γ by unfold lush; rw [neg_sub,sub_neg_eq_add,add_comm]; rfl]; exact hu.2
end YM.CF.Scion
