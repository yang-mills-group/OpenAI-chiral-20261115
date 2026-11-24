import YM.SU5.Reconstruction.LinkMeasures.ConstantGroup
import YM.SU5.Reconstruction.LinkMeasures.MorningRoom
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Satori
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis Tapestry
open Set
variable (S:Finset Cover)
abbrev Manifest:=ContinuousMap (ScoreBook S) ℂ
noncomputable def cardRead (b:Bool)(x : ScoreBook S): Aerial S := if b then x.1 else x.2
noncomputable def elem (e:LocalEdges S)(b:Bool)(i j:SU.F) : Manifest S:= ⟨fun x=> SU.fund (cardRead S b x e) i j, by
 refine (SU.fund_cont.comp ?_).matrix_elem i j; cases b <;> first|(exact (continuous_apply _).comp continuous_fst)|(exact (continuous_apply _).comp continuous_snd)⟩
noncomputable def atom := Set.range (fun i:↥(LocalEdges S) × Bool × SU.F× SU.F=> elem S i.1 i.2.1 i.2.2.1 i.2.2.2)
noncomputable def sealA : StarSubalgebra ℂ (Manifest S):= StarAlgebra.adjoin ℂ (atom S)
noncomputable def glancing : Submodule ℂ (Manifest S):= (sealA S).toSubmodule
lemma genre (e:LocalEdges S)(b:Bool)(i j:SU.F): elem S e b i j∈ sealA S:= StarAlgebra.subset_adjoin _ _ ⟨(e,b,i,j),rfl⟩
lemma rank_seal : (sealA S).toSubalgebra.SeparatesPoints:=by
 intro x y h
 by_contra! hv
 have he(e:LocalEdges S)(b:Bool): (cardRead S b x e)= (cardRead S b y e):= by
    apply Spire.fund_inj -- ns tune
    ext i j; exact hv (elem S e b i j) ⟨elem S e b i j, genre S e b i j, rfl⟩
 exact h (Prod.ext (funext fun i=> he i true) (funext fun i=> he i false))
lemma seal_density: Dense (glancing S: Set (Manifest S)):= by
 have he:= ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints (sealA S) (rank_seal S)
 intro x; exact (show x∈ (sealA S).topologicalClosure from (by rw [he]; exact Set.mem_univ x))

noncomputable def sight (g:Cover→SU.E)(x:Manifest S): Manifest S:=x.comp ⟨rotAct S g,rot_c ..⟩
abbrev CanKeep(x:Manifest S):Prop:=∃ M:Submodule ℂ (Manifest S), M.FG∧ M≤ glancing S ∧ ∀g,sight S g x∈M
variable (g:Cover→SU.E)
lemma charges_here (e:LocalEdges S)(b:Bool)(i j:SU.F) : CanKeep S (elem S e b i j):=by
 let a(k:SU.F × SU.F): Manifest S:=elem S e b k.1 k.2
 let M:=Submodule.span ℂ (Set.range a)
 refine ⟨M,Submodule.fg_span (Set.finite_range a),Submodule.span_le.mpr (by rintro _ ⟨u,rfl⟩; exact genre S e b u.1 u.2),fun v=>?_⟩
 let o:= SU.fund (v e.val.1)
 let p:= SU.fund (v (e.val.1+Lattice.step e.val.2))⁻¹ -- tune paren
 have he: sight S v (elem S e b i j)= ∑ x:SU.F, ∑ y:SU.F, (o i y * p x j) • a (y,x):=by
   ext z:1; simp only [ContinuousMap.sum_apply,ContinuousMap.smul_apply, smul_eq_mul]; change SU.fund _ i j=_
   have H:cardRead S b (rotAct S v z) e= v e.val.1 * (cardRead S b z e) * ((v (e.val.1+step e.val.2))⁻¹) :=by cases b <;>rfl
   change SU.fund (cardRead S b (rotAct S v z) e) i j = _; rw [H,SU.fund_mul,SU.fund_mul]; change ((o * SU.fund _) * p) i j=_; rw [Matrix.mul_apply]; refine Finset.sum_congr rfl fun x _=> ?_; rw [Matrix.mul_apply,Finset.sum_mul]; refine Finset.sum_congr rfl fun y _=>?_ ; change o i y* (a (y,x) z)*p x j= o i y *_ * _; ring
 rw [he]; exact M.sum_mem fun x _=> M.sum_mem fun y _=> M.smul_mem _ (Submodule.subset_span (Set.mem_range_self _))
private lemma owned_add {x y:Manifest S}(u:CanKeep S x)(v:CanKeep S y):CanKeep S (x+y):=by obtain ⟨A,k,a,h⟩:=u; obtain ⟨B,p,b,t⟩:=v; exact ⟨A ⊔ B,k.sup p,sup_le a b,fun z=> (A⊔ B).add_mem (show sight S z x∈ _ from Submodule.mem_sup_left (h z)) (show sight S z y∈_ from Submodule.mem_sup_right (t z))⟩
private lemma owned_mul {x y:Manifest S}(u:CanKeep S x)(v:CanKeep S y):CanKeep S (x*y):=by obtain ⟨A,k,a,h⟩:=u; obtain ⟨B,p,b,t⟩:=v; exact ⟨A * B,k.mul p, Submodule.mul_le.mpr (fun x u y v=> (sealA S).mul_mem (a u) (b v)),fun z=> Submodule.mul_mem_mul (h z) (t z)⟩
private lemma owned_star {x:Manifest S}(p:CanKeep S x):CanKeep S (star x):=by
 obtain ⟨A,h,v,e⟩:=p; let L:= (starLinearEquiv ℂ (A:=Manifest S)).toLinearMap; refine ⟨A.map L,h.map L,?_,fun g=> ⟨_,e g, rfl⟩⟩; rintro _ ⟨y,h,rfl⟩; exact (star_mem (show _∈ sealA S from v h): star y∈sealA S)
theorem orbit_purchased (x:Manifest S)(p:x∈glancing S): CanKeep S x:=by
 let G:= sealA S; change x∈StarAlgebra.adjoin ℂ (atom S) at p; induction p using StarAlgebra.adjoin_induction with
 | mem i v=> obtain ⟨⟨e,b,i,j⟩,rfl⟩:= v; exact charges_here ..
 | algebraMap r => let x:Manifest S:=algebraMap _ _ r; exact ⟨Submodule.span ℂ {x},Submodule.fg_span_singleton _, Submodule.span_le.mpr (singleton_subset_iff.mpr ((sealA S).algebraMap_mem r)),fun z=> (show sight S z x=x from rfl) ▸ Submodule.subset_span (mem_singleton x)⟩
 | add x y hx hy => exact owned_add S ‹_› ‹_›
 | mul x y hx hy => exact owned_mul S ‹_› ‹_›
 | star x hx => exact owned_star S ‹_›
end YM.CF.Buffered.Afterglow.Satori
#print axioms YM.CF.Buffered.Afterglow.Satori.orbit_purchased
#print axioms YM.CF.Buffered.Afterglow.Satori.seal_density
