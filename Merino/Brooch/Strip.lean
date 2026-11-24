import Merino.Brooch.Guild

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 520000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Brooch
open Function Finset Fock Scroll Spire Sault
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Lattice Cube Scree Skye Sour Drapes Tulip Lat Branch Swell
open Thera Hest Levier
variable {N:Side}
local notation "Jk"=> Single N

open Dial Vow

open Tenant Tap RG Salt

variable (s:Sweep N){P W:SOp N}{X:SOp N}{K:Scree.Loom N}{q l m:ℕ}
variable {p:BudgetPoint}{a b c d h t v z:ℝ}
variable {o:Site N}
local notation "post"=> node o
local notation "G"=> Fence P W K p q l ((boxA s) post) h z


local notation "D0"=> Openc (More N) d
variable {J T:Axis→ SOp N}{Y:SOp N}

/-- Full block certificate: short plus tail spurs and glaze. -/
structure Strip (P W:SOp N)(o:Site N)(m:ℕ)(a d b v:ℝ)(J T:Axis→SOp N)(X Y:SOp N):Prop where
 starts: ∀ i:Axis,Soak (node o) (J i) a b d
 shade:Soak (node o) X a b d
 ends:∀ i:Axis,Soak (node o) (T i) a v d
 endX:Soak (node o) Y a v d
 jump:∀ i:Axis,∀ z':Openc (More N) d,spur (millIntro P W) o i m z'.val=J i z'.val+T i z'.val
 hue:∀ z':Openc (More N) d,(P z'.val-tickA N)*windmill o m=X z'.val+Y z'.val

variable (A:Strip P W o m a d b v J T X Y)
variable (U' V:Pane N)(E:Staffer P W d)(u:0<d)(g:Guard V d)
local notation "M"=> voidΛ N m o
local notation "Z"=> profile V

include A E u g
lemma entire :
 dg (inward (P Z) M (W Z))= perWave p o m J false U' V + perWave p o m T false U' V:=by


 let f: Op Jk→+FC Jk:= ⟨⟨dg,by simp [dg,dyad]⟩,dg_add⟩
 change f (inward _ (windmill o m) _)=_
 rw [inwardE E V g,map_sum]; simp only [perWave,Finset.sum_apply,Pi.sub_apply]
 rw [←sum_add_distrib]
 apply sum_congr rfl; intro i _
 have h(x):=co_Set o x (J i) (T i) E i m (A.jump i) u V g
 rw [h,h,map_sub,map_add,map_add]
 change f _ + f _ - (f _+f _) =
      (f (co_Ψ (o+m•step i) o (J i) Z)- f (co_Ψ (o-m•step i) o (J i) Z))+
      (f (co_Ψ (o+m•step i) o (T i) Z)- f (co_Ψ (o-m•step i) o (T i) Z))
 abel

omit A E u g

variable (hm:p.B+2*m≤l*p.B)
local notation "core"=>grooveB l p post
variable (hv:pingS p.threshold (grooveB l p (node o)) U')
include hm hv
lemma node_lit(x:Site N)(S:LatticeFieldEstimates N)(e:separation o x ≤ m):
 paneMask p x true S U' = S U':=by
 apply Set.indicator_of_mem
 change pingS _ _ _
 intro i v; refine hv _ ?_;exact fun t=>v (Disjoint.mono (offsetFit o x e hm) le_rfl t)


lemma jump_lit : perWave p o m J true U'=perWave p o m J false U':=by
 unfold perWave; rw [Finset.sum_apply, Finset.sum_apply]
 refine sum_congr rfl fun i _=>?_
 rw [Pi.sub_apply,Pi.sub_apply,boom,boom,node_lit U' hm hv _ _ (stopBeam o i m).1,node_lit U' hm hv _ _ (stopBeam o i m).2]; rfl

include A E u g

lemma lit :
   leanLatticeFieldEstimates p o m J X U' V= front P W M U' V-tailLatticeFieldEstimates p o m T Y U' V:=by
 unfold leanLatticeFieldEstimates
 simp only [Pi.add_apply,node_lit U' hm hv _ _ (le_of_eq_of_le (separation_self o) (Nat.zero_le _)), jump_lit U' hm hv]
 unfold front kerLocal tailLatticeFieldEstimates
 rw [entire (p:=p) A U' V E u g]
 let y:↥(D0):=⟨profile V,V,g,by simpa using u⟩ -- specify
 rw [show (P Z-tickA N)*M=X Z+Y Z from A.hue y,Matrix.trace_add,add_smul]
 simp only [Pi.sub_apply,shank,strike,metal, Pi.add_apply]
 abel


omit E u g hv
local notation "core'"=> grooveB l p (boxA s post)
variable (D:DockPulse p K t d a h z l q)(B:Steers s P W d)
include D B
lemma alight :
 houseK p core' (scene0 s K (leanLatticeFieldEstimates p o m J X)) =
 houseK p core' (scene0 s K (front P W M) - scene0 s K (tailLatticeFieldEstimates p o m T Y)):= by
 unfold houseK; funext i
 by_cases h0: i∈pingMask p core'
 · rw [Set.indicator_of_mem h0,Set.indicator_of_mem h0, ← call_less]
   let w:=back s i.1; let y:=back s (K i)
   have f:Guard y d:=keepC (xtra s.charge) (castX s) _ _ (D.roof.paid i)
   have e: pingS p.threshold core w:=by
     have zz:Salt.actY s {(boxA s) post}={post}:=by simp [Salt.actY]
     change pingS _ (Lattice.halo _ {post}) (flashA s i.1)
     rw [←zz,Salt.walkA, Salt.glowA];exact h0
   exact congrArg (move s) (lit A w y B.toStaffer D.pos f hm e)
 rw [Set.indicator_of_notMem h0,Set.indicator_of_notMem h0]

def ep(l m:ℕ)(p:BudgetPoint)(z h a c b v:ℝ):=
 (fhFee l p z h a c (wζ a m)+dull l m p z h a c v)+
 (bright l m p z h a c b+ bright l m p z h a c b)


variable (H :Solo a c P d)(Q:Solo a c W d)
include H Q

lemma ered :
   G (scene0 s K (leanLatticeFieldEstimates p o m J X)) (ep l m p z h a c b v)
      (dull l m p z h a c v):=by
 have y:Soak post (fun _=>M) a (wζ a m) d:=by
    convert windmillCost (d:=d) o m D.hint.le using 1
    rw [List.length_ofFn]
 have f:= ((act_front s D H Q M y B).sub
              (thick s hm D H Q A.endX A.ends)).aft (Subset.refl core')
 rw [←alight s A hm D B, zero_add] at f
 have w:= slim s hm D H Q A.shade A.starts
 have e:=f.arc (w.tee (Subset.refl core'))
 rw [add_zero, add_sub_cancel] at e
 exact e
end YM.CF.Merino.Brooch

