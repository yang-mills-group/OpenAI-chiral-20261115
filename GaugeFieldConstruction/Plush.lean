import GaugeFieldConstruction.Plum
import GaugeFieldConstruction.Frosts
import GaugeFieldConstruction.Heliac
/- Gauge average phase extensions. -/
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
variable {p:BudgetPoint} (o:Skye.Seat n)
open TableF.Lenten.Loden Haro Tap Hove Moto
attribute [local instance] opCStarAlgebra
variable {h v:ℝ}
open Dial Nacre Ember Fir Fock
open Work.F03 Taxi TableF Bank HushP ModuleB Flot RG Hake
variable {o} (M: Male)(P: Waves)
open Layout Fren
abbrev nCap {n:Side} (S: Sweep n): Hubber n≃ Hubber n where
 toFun:= MustCap (boxA S)
 invFun:= MustCap (boxA S⁻¹)
 left_inv:= fun i=> actG_l S i
 right_inv:= fun i=> by change actS S (actS S⁻¹ i)=i; simpa only [inv_inv] using actG_l S⁻¹ i -- tune
lemma tiltX(s t:Sweep n)(i:Hubber n): nCap t (nCap s i)=nCap (s*t) i:= (actG_s ..).symm
lemma tiltY(s:Sweep n)(o: Seat n): nCap s (Pach o)=Pach (sh s o):=congrArg (fun i:Scree.Hub n=> i.val.2) (move_Φ s o)
variable (r: Sweep n)
lemma tilt_atom (A:Paper n)(k:Pane n):marketD (Barber r A) (flashA r k)= lotB r.charge (Typer r) (launchZ r) (marketD A k) :=by
 change (∑ j,αLines (Barber r A) _ _ • dot_Q j)= lotB r.charge (Typer r) (launchZ r) (marketD A k); rw [boothK]; exact (exportD ..).symm
-- exact linear action on paper
lemma born_Z(A B: Paper n):Barber r (A+B)= Barber r A+Barber r B:=by
 funext i u; unfold Barber CardCraft; rw [show αLines (A+B) _= _+_ from (show αLines (A+B) (flashA r⁻¹ u)=_ from rfl), oneCκ]; rfl -- Tune
lemma born_P(A:Paper n)(b:ℂ): Barber r (b • A)=payZ r b • Barber r A:=by
 funext i u; unfold Barber CardCraft; rw [show αLines (b • A) (flashA r⁻¹ u)=b • _ from (show αLines (b • A) (flashA r⁻¹ u)=b • αLines A _ from rfl),scaleCκ]; rfl
lemma bornØ:Barber r (0:Paper n)=0:=by
 have hp:=born_P r 0 0; simpa [payZ,cSignX] using hp -- term sign
lemma tiltFee {p:BudgetPoint}{S: Hubber n}{F:Paper n}{c h:ℝ}(p':TrackD p S h F c) : TrackD p (nCap r S) h (Barber r F) (CaseL*c):=by
 obtain ⟨L,q,v⟩:=p'; refine ⟨_,fun i=> trade_G _ _ _ _ _ _ (massTransitS p r) L q i,(wardPay _ _ _ (fun i=> (q i).1.1) _).trans (mul_le_mul_of_nonneg_left v (by positivity))⟩ -- tune
abbrev tiro (T: Torches n):Torches n:=(Barber r T.1,fun i=> Barber r (T.2 ((nCap r).symm i)))
lemma crown_D(t:Sweep n)(F:Torches n): tiro t (tiro r F)=tiro (r*t) F:=by
 apply Prod.ext (barber_L ..); funext i; change Barber t (Barber r (F.2 _))= Barber (r*t) (F.2 _);
 rw [barber_L,show (nCap r).symm ((nCap t).symm i)=(nCap (r*t)).symm i from ?_]; apply (nCap (r*t)).injective; rw [←tiltX, Equiv.apply_symm_apply, Equiv.apply_symm_apply,Equiv.apply_symm_apply]
lemma tiro_fee(F: Torches n){h a c d:ℝ}(u:Inscribe p o h a F c d):Inscribe p (sh r o) h a (tiro r F) (CaseL*c) (CaseL*d):=by
 refine ⟨(show TrackD p (Pach _) _ _ _ from (tiltY r o) ▸ tiltFee r u.1),?_⟩; obtain ⟨V,q,w⟩:=u.2; let K:=nCap r; let Y:= F.2;
 refine ⟨fun i=> CaseL * V (K.symm i), fun i=> ?_,?_⟩
 · obtain ⟨i,rfl⟩:=K.surjective i; refine ⟨?_,fun v=>?_⟩
   · change TrackD p (K i) h (Barber _ (Y (K.symm (K i)))) (CaseL * V (K.symm (K i))); rw [K.symm_apply_apply]; exact tiltFee r (q i).1
   change Barber _ (Y (K.symm (K i)))=_; rw [K.symm_apply_apply, show Y i= _ from (q i).2 (fun j=>v ⟨mem_map_of_mem _ j.1, Hive.grove_t i r j.2⟩),bornØ]
 rw [←K.sum_comp (fun i:Hubber n=> rent a i *(CaseL *V (K.symm i)))]; have hp(i:Hubber n):rent a (K i)=rent a i:=by unfold Branch.rent; rw [show (K i).card=i.card from card_map ..]
 simp_rw [hp,K.symm_apply_apply,mul_left_comm (rent _ _),← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left w (by positivity)
lemma tiro_add(X Y:Torches n):tiro r (X+Y)=tiro r X+tiro r Y:= Prod.ext (born_Z ..) (funext fun i=> born_Z ..)
lemma tiro_P(X:Torches n)(c:ℂ): tiro r (c • X)=payZ r c • tiro r X:= Prod.ext (born_P ..) (funext fun i=> born_P ..)
lemma tilt_T(F:Torches n)(u: Pane n):Ion (tiro r F) (flashA r u)=lotB r.charge (Typer r) (launchZ r) (Ion F u):=by
 rw [optics_T,optics_T,map_add,map_sum]; apply congrArg₂ (·+·) (tilt_atom ..)
 symm; apply Fintype.sum_equiv (nCap r); intro i; let K:=nCap r; change _=marketD (Barber r (F.2 (K.symm (K i)))) (flashA r u); rw [K.symm_apply_apply,tilt_atom]
lemma citizen_port(F:Torches n)(p:LegTax F):LegTax (tiro r F):=⟨barber_tru F.1 1 r p.1,fun i=> barber_tru _ 1 r (p.2 _)⟩ -- tune args automatically omitted g?
open Urn
-- precision.Echo across Mark. use transport raises via Sector. no opposite lift sign required. use dim.
abbrev Surf(r:Sweep n): FC (Single n)→+* FC (Single n):= lotB r.charge (Typer r) (launchZ r)
private lemma twist_F {I:Type}[DecidableEq I][Fintype I](U:UNI I):Injective (twist U):=fun a b p=>by rw [←twist_inv U a,p,twist_inv]
private lemma wind_D{I:Type}[DecidableEq I][Fintype I](b: Bool)(U:Op I)(V:Op I)(u:windX b U=windX b V):U=V:=by cases b; exact u; change cc U=cc V at u; rw [←cc_cc U, u, cc_cc]
lemma Surf_inj: Injective (Surf r):=by
 intro x y t; unfold Surf lotB at t; change Spire.tourP _ _ _ _= Spire.tourP _ _ _ _ at t; unfold Spire.tourP at t; split_ifs at t with he
 · apply wind_D r.charge; exact wind_D true _ _ (twist_F _ (show theta (launchZ r) _= _ from t))
 exact wind_D r.charge _ _ (twist_F _ t)
lemma scuff_step (X: Hubber n)(a b:Single n)(p: (launchZ r).val a b≠0)(q:b ∈Scuff X): a∈ Scuff (nCap r X):=by
 let f:= boxA r; have hp:f (aptK a)=aptK b:=Tye.birth_l a b (castX r) (spinU r.charge r.s) r.charge p -- missing arg
 exact mem_filter.mpr ⟨mem_univ _,mem_map_equiv.mpr (hp.symm ▸ (mem_filter.mp q).2)⟩
private lemma holo_B (u:Hake.Oboe (Single n)){S: Hubber n}(p:u.2∈Scuff S): Sector (Scuff (nCap r S)) true (Surf r (bell u)):=by
 let L:= launchZ r; rw [Surf,Urn.mole]; unfold roseB; apply Sector.sumS; intro j _; by_cases h: sewV L (Typer r) u j=0 -- tune order
 · rw [h,zero_smul]; apply Sector.zero
 apply Sector.scale; have hp:=scuff_step r S j.2 u.2 (?_: L.val j.2 u.2 ≠0) p; rcases j with ⟨a,b⟩; cases a; exact Sector.down b hp; exact Sector.up _ hp; exact fun v=>h (spice_E _ _ _ _ v)
lemma surf_C (S: Hubber n){b: Bool}{A: FC (Single n)}(u:Sector (Scuff S) b A): Sector (Scuff (nCap r S)) b (Surf r A):=by
 induction u with
 | zero b=> rw [map_zero]; apply Sector.zero
 | one=> rw [map_one]; apply Sector.one
 | up i v=> exact holo_B r (true,i) v
 | down i v=> exact holo_B r (false,i) v
 | add _ _ ih hi=> rw [map_add]; exact ih.add hi
 | mul _ _ ih hi=>rw [map_mul]; exact ih.mul hi
 | scale _ c ih=> rw [show Surf r (c • _)= cSignX _ c • _ from visage ..]; exact ih.scale _
-- poster laws sufficiency for all spectators locally.Density conservative.
abbrev Surface : FC (Single n)→ₗ[ℝ] FC (Single n) where
 toFun:= Surf r
 map_add':=map_add _
 map_smul':=fun v f=>by change Surf r _= v • Surf r f; rw [←Complex.coe_smul, ←Complex.coe_smul,show Surf r _=_ from (show Surf r ((v:ℂ) • f)=_ from visage r.charge (Typer r) (launchZ r) f v)]; simp [cSignX]
noncomputable def Sback: FC (Single n)≃L[ℝ] FC (Single n):= (LinearEquiv.ofBijective (Surface r) ⟨Surf_inj r,LinearMap.injective_iff_surjective.mp (show Injective (Surface r) from Surf_inj r)⟩).toContinuousLinearEquiv.symm
lemma SbackFee (x:FC (Single n)):Surf r (Sback r x)=x:= (Sback r).symm_apply_apply x
private abbrev BaseS (S:Hubber n) : Submodule ℝ (FC (Single n)) where
 carrier:= {i|Sector (Scuff S) false i}
 zero_mem':=Sector.zero _
 add_mem':= @fun x y p q=> Sector.add p q
 smul_mem':=fun v x u=> (by rw [←Complex.coe_smul]; exact Sector.scale u _)
private def μS(S:Hubber n) : BaseS S →ₗ[ℝ] BaseS (nCap r S):= (Surface r).restrict (p:=BaseS S) (fun i h=> surf_C r _ h)
private lemma in_S(S:Hubber n): Injective (μS r S):=fun i j h=>Subtype.ext (Surf_inj r (congrArg Subtype.val h))
lemma Stem_back (S:Hubber n)(x:FC (Single n))(p: Sector (Scuff (nCap r S)) false x): Sector (Scuff S) false (Sback r x):=by
 have he: Module.finrank ℝ (BaseS S)=Module.finrank ℝ (BaseS (nCap r S)):=by
    have hp(k:Sweep n)(T:Hubber n):Module.finrank ℝ (BaseS T) ≤ Module.finrank ℝ (BaseS (nCap k T)):=LinearMap.finrank_le_finrank_of_injective (in_S k T)
    exact le_antisymm (hp r S) ((hp r⁻¹ (nCap r S)).trans_eq (congrArg (fun i=> Module.finrank ℝ (BaseS i)) ((nCap r).symm_apply_apply S)))
 obtain ⟨a,g⟩:= (LinearMap.injective_iff_surjective_of_finrank_eq_finrank he|>.mp (in_S r S)) ⟨x,p⟩
 rw [Surf_inj r ((SbackFee r x).trans ((show Surf r a.val=x from congrArg Subtype.val g).symm))]; exact a.property
abbrev CarrX (S:Hubber n)(F:marker0 n):Prop:= LocalOn S F ∧ ∀ i:Pane n,Sector (Scuff S) false (F i)
abbrev Distant(o:Seat n) (F:marker0 n):Prop:= Envelope F ∧∃ S:Hubber n, Disjoint (Pach o) S∧ CarrX S F
abbrev SkiM (F:marker0 n):marker0 n:= Sback r ∘ F ∘ flashA r
lemma Ski_D (F:marker0 n)(p:Distant (sh r o) F): Distant o (SkiM r F):=by
 obtain ⟨p,X,h,v,f⟩:=p; let i:= (nCap r).symm X; obtain ⟨X,rfl⟩:= (nCap r).surjective X; let A:= flashA r; have he:(nCap r X).map (boxA r).toEmbedding=X:=by ext; simp only [nCap,Equiv.coe_fn_mk,MustCap,mem_map_equiv]; simp
 refine ⟨Girt.pole_w _ (Sback r) (Sback r).continuous (show Envelope (F ∘ A) from Env.along p (revM r).measurable),X,fun W p q=> ?_,fun i j u=>congrArg (Sback r) (v _ _ (flashD r i j _ (he.symm ▸ u))),fun i=> Stem_back r _ _ (f _)⟩ -- tune disjoint definition and envelope TC
 intro y z; exfalso; refine Finset.disjoint_left.mp h (?_: (boxA r).symm y∈ _) ?_; · rw [←tiltY]; exact mem_map_of_mem (boxA r).symm.toEmbedding (p z)
 exact mem_map_of_mem _ (q z)
end MastTin
end YM.CF.XGarden
end
