import YM.SU5.FiniteGaugeData.Jadot.Chisel
import YM.SU5.FiniteGaugeData.Lycan.Piper
import YM.SU5.FiniteGaugeData.CodaT.SummitB
import YM.SU5.FiniteGaugeData.CodaT.Swirl
/-! # Color-specific tilted contract. Arbitrary many-body. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 410000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Window.Brique
open Reed (Fine)
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
open Heat Quest Fock.Brique
open Nacre Heat Charm Chrono Journey
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
open SalonG
open Quest.Chaperone
open Steam
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l)) {g:ℝ}{u v:ℕ→ℕ}
open Eight YM.SU5.FiniteGaugeData.CodaT YM.SU5.FiniteGaugeData.Cuprite.Spirit YM.SU5.FiniteGaugeData.Cuprite.Spirit.Vapors Fock.Relief Rhythm.Hush Rhythm.CodaT Dial Aria Reduction.Drama.Pack
open Rhythm.Dolores Rhythm.Ergo Hills Gamer Fock.Reduction Turnist Alts Alts.Emblem Window.Presidio.Nigra
namespace Chiffon
open Moorend Rhythm.CodaT
open Reduction.Loyd Reduction.Dijon Reduction.Loyd.Art Reduction.Celeste
namespace Sesame
open Reduction Lycan Niagara Chisel Largo Mirage Cascade Ember PolarF Onyx
-- formation family I separate from launch etc. Allows fixed labels but variable clocks/separations. Vectors wrap from cover at phases.N.
abbrev Grit:= Niagara.Chisel
variable {ι:Type*} (F:ι→Grit)
abbrev roof (Y Z:Grit): Grit:= ⟨Y.σ,Y.launch,Z.landing,Lattice.route (nodeC Y.launch) (nodeC Z.landing) 1,Lattice.route_end ..,Y.u,Z.d,Y.up,Z.dn⟩
local notation "Μ"=>ι×SU.Slot
abbrev uEnd(N:Side)(v:ι×SU.Slot):= basisC N (F v.1).launch (F v.1).u v.2
abbrev dEnd(N:Side)(v:ι×SU.Slot):= basisC N (F v.1).landing (F v.1).d v.2
abbrev Techn(v:ι):= Window.colors (F v).σ
abbrev bookFee(K:Calibration)(X:Grit): W K:= (X.DesireB K).paid
abbrev courtI (K:Calibration)(X:List ι):W K:= (X.map (bookFee K ∘ F)).prod
abbrev lips (X:List ι): Paint:= (X.map (ProbeCode.score ∘ F)).prod
-- allow reflected later substitutions.S.
def Crest(A:Finset Cover)(F:ι→Finset Cover) : List ι→ Finset Cover
 | []=> A
 | x::X=> F x∪ Crest A F X
-- support explicit
abbrev band(X:List ι):=Crest {(0:Cover)} (fun x=> (F x).town) X
-- authentication; general transport to same stencil
lemma jungle {K:Calibration}{S:ι→Finset Cover}{A:Finset Cover}{W':ι→ W K}{G:ι→ Paint}(hp:∀ i:ι, Auth K (S i) (W' i) (G i))(p:A.Nonempty)(X:List ι): Auth K (Crest A S X) ((X.map W').prod) ((X.map G).prod):=by
 induction X with
 | nil=> exact Auth.unitP K p
 | cons x X ih=> exact ((hp x).stock_P (subset_union_left)).prodP (ih.stock_P subset_union_right)
lemma tribes(K:Calibration)(X:List ι):Auth K (band F X) (courtI F K X) (lips F X):= jungle (fun i=>ProbeCode.Country K (F i)) (by simp) X -- comp def
section
variable (N:Side)(M:Male)
variable (h: Standing (tickA N) (spar 4 M (1: Pane N)))
local notation "P"=> spar 4 M (1: Pane N)
local notation "Q"=> tickA N
lemma siphon (i j:Μ): inner ℂ (dEnd F N j) (uEnd F N i)=0:=by
 let U:=F i.1; let V:=F j.1; let W:= roof U V; have he: Lifted.index N V.landing V.d j.2≠ Lifted.index N U.launch U.u i.2:=fun t=> Chisel.unequal W N (congrArg Prod.fst t)
 unfold dEnd uEnd basisC; rw [inner_smul_left,inner_smul_right,basis_inner,basis_apply]; rw [if_neg he,mul_zero,mul_zero]
lemma dgreen (i:ι): ProbeCode.score (F i) N 1= tribe (Techn F) (uEnd F N) (dEnd F N) i:=by
 let W:= F i; let D:= W.buyD N 1; let U:=W.upCard N; let V:=W.downCard N; let f(u v: Single N):= D u v • (put u*takeF v); let z:= Techn F i
 let A(p:SU.Slot):= Lycan.mark (uEnd F N) (dEnd F N) (i,p) (i,p)
 have hp (j:SU.Slot): A j= W.shiftSign N • (put (U,j)*takeF (V,j)):=by unfold A Lycan.mark uEnd dEnd basisC; rw [map_smul,Fock.remove,map_smul,create_put, create_put, star_smul, Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul]; rfl
 change ∑ i:Single N,∑ j:Single N,f i j=∑ i∈z,A i
 have he(a b:Mini N)(p q:SU.Slot):D (a,p) (b,q)=(if a=U∧b=V∧p∈z∧p=q then W.shiftSign N else 0):=W.at_off ..
 have hu(a:Mini N)(p:SU.Slot): (∑ v,f (a,p) v)=if a=U∧p∈ z then A p else 0:=by
    rw [sum_eq_single (V,p)]; unfold f; rw [he]; by_cases e:a=U ∧ p∈z; · rw [if_pos ⟨e.1,rfl,e.2,rfl⟩,if_pos e,e.1]; exact (hp p).symm
    rw [if_neg (fun h=>e ⟨h.1,h.2.2.1⟩),if_neg e,zero_smul]; intro j _ h; rcases j with ⟨b,q⟩; unfold f; rw [he,if_neg fun t=>h (Prod.ext t.2.1 t.2.2.2.symm),zero_smul]; simp
 rw [show ∑ i:Single N,∑ j:Single N,f i j= _ from Fintype.sum_prod_type (fun i: Mini N×SU.Slot=> ∑ j:Single N,f i j)]; simp_rw [hu]; rw [sum_eq_single U]; simp ; all_goals simp_all
lemma solarEntry (Y Z:Grit) (p q:SU.Slot): Niagara.main M N (Z.downCard N,p) (Y.upCard N,q)= if p=q then reedsK M N (Z.downCard N) (Y.upCard N) else 0:=by
 let Ψ:= Niagara.main M N; let A:= Y.upCard N; let B:= Z.downCard N; let W:=roof Y Z; have hx:B≠ A:= Chisel.unequal W N
 unfold Niagara.main hubK; rw [Matrix.kroneckerMap_apply]; change (((1+reedsK M N)*cutM (ruddy N)) B A *_) =_; rw [Largo.compass',if_pos (mem_product.mpr ⟨mem_univ _,Y.up⟩),Matrix.add_apply,Matrix.one_apply_ne hx]; by_cases h:p=q<;> simp [Matrix.one_apply,h,B,A]
abbrev Otter (C:Grit→Grit→ℂ)(F:ι→Grit)(x y:ι×SU.Slot):ℂ:=if x.2=y.2 then C (F x.1) (F y.1) else 0
abbrev cello(N:Side)(M:Male)(i j:Grit):ℂ:= (roof i j).stage N M
abbrev aroma(i j:Grit):ℂ:= (roof i j).finalIncome
include h
lemma livPrice (x y:Μ): cupE Q P (uEnd F N x) (dEnd F N y)= Otter (cello N M) F x y:=by
 unfold cupE uEnd dEnd basisC; let U:=F x.1; let V:= F y.1; let W:= roof U V; rw [map_smul,inner_smul_left,inner_smul_right,basis_inner,basis_act,pinF M N h]; change star _* (_ * (Niagara.main M N (V.downCard N,y.2) (U.upCard N,x.2)))=_; rw [solarEntry]; unfold Otter; by_cases p:y.2=x.2; swap; · rw [if_neg p,if_neg (Ne.symm p),mul_zero,mul_zero]
 rw [if_pos p,if_pos p.symm, ←mul_assoc,mul_comm (star _)]; change W.shiftSign N*reedsK M N (W.downCard N) (W.upCard N)=W.stage N M; rw [W.modeCost M N,←mul_sum,inv_mul_eq_div]; unfold Chisel.stage; push_cast; rfl -- tune
lemma inkEarn(X:List ι): Volt Q P (lips F X N 1)= Conv (Techn F) (Otter (cello N M) F) X:=by
 have hp(Y:List ι):lips F Y N 1= Coral (Techn F) (uEnd F N) (dEnd F N) Y:= by
    induction Y with
    | nil=>rfl
    | cons i X ih=> change (ProbeCode.score (F i) N 1 * lips F X N 1)= _*_; rw [dgreen F N i,ih]; rfl
 rw [hp,Bodice]; simp_rw [livPrice F N M h]; exact h; exact siphon F N
omit h
-- then can permit reflect
end
#print axioms inkEarn
end Sesame
end Chiffon
end YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
