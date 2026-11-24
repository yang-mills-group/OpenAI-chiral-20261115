import GaugeFieldConstruction.Virago
import GaugeFieldConstruction.Esther
import GaugeFieldConstruction.Polder
import GaugeFieldConstruction.Sotto
import GaugeFieldConstruction.Soapstone
set_option autoImplicit false
set_option maxRecDepth 5500
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
namespace MastTin
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
namespace ArtCart
open Buffered Lifted Girt Skye Window Vale
variable {x y:Cover}{d:ℕ}{k:Side}
open TableF TableF.Lenten Layout Flot Moto Tap Bank ModuleB Haro Hove Fren Work.F03 Taxi Ember Fir HushP
variable {F H:Paper n}{p:BudgetPoint}{c v h r:ℝ}(M: Male){o:Seat n}
open Spectrix Simmer Next.Rank.Spindle
open Gleam Gleam.Guide Fock.Flux
open Py.Rate.LocalLimit.Papal Py.Rate.LocalLimit.Papal.FrameP
-- θ.Ship manifestation $pR`. Tick frame transport from **fixed** Reifier to any actual $l$.
open AnalyticBridge VerifiedReset
open Gleam.Guide.Pitcher Coins Fock.Flux Fock.Flux.Pacts YM.GaugeFieldConstruction
local notation "Sp"=>Cauchy.Spin
open scoped Kronecker
lemma polar_null (L:tangD n →ₗ[ℝ] ℂ)(t:∀ (g:SU.E)(u:tangD n),L (colorMove g u)=L u)(u:tangD n): L u=0:=by
 let X:=Edge (Site (More n)); let Q(i:X):=LinearMap.single ℝ (fun _:X=>SU.group.Color) i
 have hp(i:X)(v:SU.group.Color): L (Q i v)=0:=by
    let T:=L.comp (Q i); have he:T=0:=by
       apply StressFlux.linear_invariant Thera.yet_one -- namespace tune
       intro g v; change L (Q i _) = _; rw [show Q i (SU.group.adjoint g v)=colorMove g (Q i v) from ?_ ,t]; rfl
       ext1 l; unfold Q; change Pi.single (M:=fun _:X=> SU.group.Color) i (SU.group.adjoint g v) l = SU.group.adjoint g (Pi.single (M:=fun _:X=> SU.group.Color) i v l); by_cases h:l=i; subst l; simp; simp [Pi.single_apply,h]
    exact DFunLike.congr_fun he _
 rw [← show ∑ i:X,Q i (u i)=u from (by ext1 i; simp [Q,Finset.sum_apply,Pi.single_apply]; rw [sum_eq_single i]; simp; intro c _ g; simp [Ne.symm g]; simp),map_sum]; simp_rw [hp]; simp
abbrev αslot (x:Site n)(i: SpinIdx)(y:SU.Slot):Single n:= ((x,i),y)
lemma polar_matrix (g:SU.E)(A B: Op (Single n))(p y:Site n)(i j:SpinIdx)(h:matPH B p y* KinX g=KinX g*matPH A p y): ∑ k:SU.Slot,B (αslot p i k) (αslot y j k)= ∑ k:SU.Slot,A (αslot p i k) (αslot y j k):=by
 let Tp (M:Op (Single n)):Op SU.Slot:= Matrix.of fun k l=>M (αslot p i k) (αslot y j l); let u:UNI SU.Slot:= SU.matter g
 have hv:Tp B*u.val=u.val*Tp A:=by
    ext k l; let H:= KinX g; let F:=matPH A p y; let G:=matPH B p y; have h:= Matrix.ext_iff.mpr h (i,k) (j,l); change (G*H) _ _ = (H*F) _ _ at h
    have he(k l w):H k (l,w)= if k.1=l then u.val k.2 w else 0:=by unfold H KinX; rw [Matrix.kronecker_apply]; simp [Matrix.one_apply,ite_mul,u,show mater g=(SU.matter g).val from rfl] -- tune
    simp_rw [Matrix.mul_apply,Fintype.sum_prod_type,he] at h -- trouble he only matches RHS H (i,k) b (s,Tp) AND H (z,b) (j,l)
    -- $F.matrix$
    simp only [ite_mul,mul_ite,zero_mul,mul_zero,Finset.sum_ite_irrel,Finset.sum_const_zero, Finset.sum_ite_eq,Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at h -- tune
    simp_rw [Matrix.mul_apply,Fintype.sum_prod_type]; exact h
 have ht:Tp B= twist u (Tp A):=by rw [twist_formula,←hv,mul_assoc, u.property.2,mul_one]
 change (Tp B).trace=(Tp A).trace; rw [ht,trace_twist]
lemma traced_E (F:Paper n)(o:Skye.Seat n)(V:ℝ)(t:F∈ Glamor o Genre.mixed V)(w:300<n.val)(p y:Site n)(i j:SpinIdx) (U:tangD n) : ∑ l:SU.Slot, Paint (AlphaY F) U (αslot p i l) (αslot y j l)=0:=by
 obtain ⟨P,h,t',h0,e,d,z,H,T⟩:=Glamor_votes t w; let K:= sprig o z e d H
 let X:=AlphaY F; let L: tangD n→ₗ[ℝ]ℂ:=⟨⟨fun i'=>∑ l:SU.Slot, (panLinear X i') (αslot p i l) (αslot y j l),fun x y'=>by rw [map_add]; simp only [Matrix.add_apply,sum_add_distrib] ⟩,fun b k=>by change (∑ l:SU.Slot,(panLinear X (b • k)) (αslot p i l) (αslot y j l))= b • ∑ l:SU.Slot,(panLinear X k) (αslot p i l) (αslot y j l); rw [map_smul]; simp only [smul_sum, Matrix.smul_apply] ⟩ -- tune
 change L U=0; exact polar_null L (fun g T=> polar_matrix g _ _ p y i j (mercy K _ _ _ T)) U
-- elementary Spin availability
lemma bandη (r:Bool): Injective (Cauchy.band r):=by intro i j h; cases r<;> fin_cases i<;> fin_cases j<;> (first|rfl|contradiction)
lemma bandE (r:Bool)(i:SpinIdx)(h:(i∈plusHalf)↔ r=false): ∃ j:Sp,Cauchy.band r j=i:=by
 revert i; cases r <;> decide
abbrev ArcK(x:Cover):Type:= ridge x 24 × Sp × SU.Slot
abbrev Mct (b:Bool)(i:ArcK x): mort x 24:= (i.1,Cauchy.band b i.2.1,i.2.2)
lemma Mct_I (x:Cover)(b:Bool):Injective (Mct (x:=x) b):=fun i j h=> Prod.ext (congrArg (fun i:mort x 24=>i.1) h) (Prod.ext (bandη b (congrArg (fun i:mort x 24=>i.2.1) h)) (congrArg (fun i:mort x 24=>i.2.2) h))
abbrev bet0 (x:Cover)(b:Bool)(i j:ArcK x): crestCard x:= some (if b then (b,Mct false i,Mct true j) else (b,Mct true j,Mct false i))
def DRy(c:crestCard x) : Prop:= c=none ∨ ∃ b i j,c= bet0 x b i j
lemma mapStem (F:Paper n)(T:Tuned F)(x:Cover)(i:crestCard x)(h:F (hereV n i)≠0): DRy i:=by
 rcases i with _|⟨b,i,j⟩; · exact Or.inl rfl
 right; obtain ⟨p,v,l⟩:= (show letters (hereV n (some (b,i,j))) from T _ h)
 have he(i:mort x 24): hereF n i∈ Tset n ↔ i.2.1∈ plusHalf:= κv (hereF n i)
 have hp(i:mort x 24)(t:Bool)(h': (t ↔ i.2.1∈plusHalf)):∃ V:ArcK x,i=Mct (!t) V:=by
    obtain ⟨v,h⟩:=bandE (!t) i.2.1 (h'.symm.trans (by cases t<;> simp)); exact ⟨(i.1,v,i.2.2),Prod.ext rfl (Prod.ext h.symm rfl)⟩
 cases b
 · obtain ⟨V,hx⟩:=hp i false (by exact ⟨nofun, fun z=> (mem_compl.mp p (he i|>.2 z)).elim⟩); obtain ⟨W,hm⟩:= hp j true (by exact ⟨fun _=> ((he j).1 v),fun _=> rfl⟩); subst i; subst j; exact ⟨false,W,V,rfl⟩
 obtain ⟨V,hx⟩:=hp i true (by exact ⟨fun _=> he i|>.1 p, fun _=>rfl⟩); obtain ⟨W,hm⟩:= hp j false (by exact ⟨nofun, fun z=> (mem_compl.mp v (he j|>.2 z)).elim⟩); subst i; subst j; exact ⟨true,V,W,rfl⟩
abbrev SwivK (x:Cover) := Option (Bool × ArcK x × ArcK x)
def pinchM : SwivK x→ crestCard x
| none=>none
| some (b,v,w)=> bet0 x b v w
lemma pinchI (x:Cover):Injective (pinchM (x:=x)):=by
 intro i j h; rcases i with _|⟨b,i,j'⟩<;> rcases j with _|⟨c,u,v⟩
 · rfl
 · simp [pinchM,bet0] at h
 · simp [pinchM,bet0] at h
 cases b<;>cases c<;> first|contradiction|(simp [pinchM,bet0,(Mct_I x false).eq_iff,(Mct_I x true).eq_iff] at h <;> simp_all)
lemma sortIQ {E:Type}[AddCommMonoid E](x:Cover)(F: crestCard x→E)(p: ∀ i,¬DRy i→ F i=0): (∑ i,F i) = F none+∑ i:ArcK x,∑ j:ArcK x,(F (bet0 _ true i j)+F (bet0 _ false i j)):=by
 let D:= pinchM (x:=x); let H:=univ.image D; rw [←sum_subset (subset_univ H) (fun i _ v=> ?_)]; swap
 · apply p; rintro (rfl|⟨t,j,k,rfl⟩); exact v (mem_image.mpr ⟨none,mem_univ _,rfl⟩); exact v (mem_image.mpr ⟨some (t,j,k),mem_univ _,rfl⟩)
 rw [show H=_ from rfl,sum_image (pinchI x).injOn,show (∑ i:SwivK x,F (D i))=_ from (Fintype.sum_option ..),Fintype.sum_prod_type]; change F none+_=_; rw [Fintype.sum_bool]; simp only [Fintype.sum_prod_type,sum_add_distrib]; try rfl -- tune
#print axioms pinchI
#print axioms Mct_I
#print axioms traced_E
#print axioms sortIQ
end ArtCart
end MastTin
end YM.CF.XGarden
end
