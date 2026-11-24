import GaugeFieldConstruction.Liberate
import GaugeFieldConstruction.TopSail
import GaugeFieldConstruction.ManifestU
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
variable {x y:Cover}{d:ℕ}{k:Side}{p:BudgetPoint}{u:ℝ}
open TableF TableF.Lenten Layout Flot Moto Tap Bank ModuleB Haro Hove Fren Work.F03 Taxi Ember Fir HushP
-- ping even inherited small-grid poses with identification
lemma pring (n:Side)(V:Pane n): pingV x d u (onC n V) ↔ pingS u ((cartO x d).image (wrap (More n))) V:=by
 refine ⟨?_,ping_K x d V⟩; rintro h ⟨i,p⟩ l; obtain ⟨j,w,t⟩:= Finset.not_disjoint_iff.mp l; obtain ⟨k,v,rfl⟩:= mem_image.mp w; obtain ⟨r,rfl⟩ :∃ r:Cover,i=wrap (More n) r:= ⟨_,(Rush.nat_true i).symm⟩; rw [touchK] at t; obtain ⟨m,u',p'⟩:= mem_image.mp t; let f:= k-m; have he:wrap (More n) f=0:=by unfold f; rw [map_sub,p',sub_self]
 have hv: k∈deckQ (r+f) p:=by
    have hh : m+f∈ deckQ (r+f) p:=by
       simp [deckQ,square_corners] at u' ⊢; rcases u' with u|u|u|u <;>(rw [u];simp [add_right_comm r f,add_right_comm (r+_) f]) -- tune
    rwa [show m+f=k from (by unfold f; abel)] at hh
 have hz:= h (r+f) p (Finset.not_disjoint_iff.mpr ⟨k,v,hv⟩); rw [onE, map_add, he,add_zero] at hz; exact hz
-- gates move on any Carto. X3 exact. archive.T
lemma mot_A (s:Shape): (cartO x d).image s.motion=cartO (s.motion x) d:=by
 ext i; nth_rw 2 [←rise_E s i]; rw [mem_image]; refine ⟨fun ⟨j,h,p⟩=>?_ ,fun p=>⟨Origin s i,(motion_C s _).1 p,rise_E s i⟩⟩; rw [rise_E, ←p]; exact (motion_C s _).2 h -- nth tune
lemma ping_trans (s:Shape)(p:Bool)(V:Pane n): pingV (s.motion x) d u (onC n V) ↔ pingV x d u (onC n (flashA (Levier.ray p s) V)):=by
 rw [pring,pring]; -- imported glowA
 let K:= Levier.ray (N:=n) p s; let Q:=boxA K; let E:= (cartO x d).image (wrap (More n)); have he: (cartO (s.motion x) d).image (wrap (More n))=E.map Q.toEmbedding:=by
    unfold E; rw [←mot_A s, image_image,map_eq_image,image_image]; exact image_congr fun i _=> (box_origin s p _).symm -- tune
 rw [he]; have hx: actY K (E.map Q.toEmbedding)= E:=by change Finset.map _ _=E; change Finset.map Q.symm.toEmbedding (Finset.map Q.toEmbedding E)=E; rw [Finset.map_map]; ext; simp [Q] -- tune
 change _ ↔ pingS _ E (flashA K V); have hh:=glowA u (E.map Q.toEmbedding) K V; rw [hx] at hh; exact hh.symm -- tune
-- universal generated probes
abbrev inkB(i:jungle x d):Prop:= i.elim True fun ⟨b,j,k⟩=> (b ↔ j.2.1∈plusHalf)∧(((!b)=true)↔ k.2.1∈plusHalf)∧ j.1.val ≠ k.1.val
lemma Tune_p (H:Paper n)(r:Tuned H)(i:jungle x d)(g:Pvi n x d H i≠0): inkB i:=by
 have he:= r (hereV n i) (fun h=> g (funext fun V=>by simp [Pvi,h])); rcases i with _|⟨b,j,k⟩; · trivial
 have h: j.1.val ≠ k.1.val:= fun x=> he.2.2 (congrArg (wrap n : Cover→Site n) x)
 let p:= highSea n b; have hx:hereF n j∈p:=he.1; have hv:hereF n k∈highSea n (!b):=he.2.1
 cases b
 · refine ⟨?_,?_,h⟩; simp only [Bool.false_eq_true,false_iff]; exact fun x=> Finset.mem_compl.mp hx ((κv _).2 x); exact ⟨fun _=> (κv _).1 hv,fun _=>rfl⟩ -- tune goals sequencing
 refine ⟨?_,?_,h⟩; · exact ⟨fun _=>(κv _).1 hx,fun _=>rfl⟩
 simp only [Bool.not_true,Bool.false_eq_true,false_iff]; exact fun x=> Finset.mem_compl.mp hv ((κv _).2 x)
def glorified (F:Psu x d)(i:jungle x d)(q:ℝ)(V: PairsC) :ℂ:= if pingV x d q V.1 then F i V.1 else 0
def showroom (K:Calibration)(i:jungle x d): Buffered.Family K:= i.elim 1 fun ⟨b,j,h⟩=> if b then creation K j.1.val j.2.1 j.2.2*removal K h.1.val h.2.1 h.2.2 else removal K j.1.val j.2.1 j.2.2 *creation K h.1.val h.2.1 h.2.2
def John (F:Psu x d)(K:Calibration)(u:ℝ): Buffered.Family K:= ∑ i:jungle x d,scalar K (glorified F i u)* showroom K i
lemma show_t (K:Calibration)(i:jungle x d)(m:Side)(V: Fields (K.c m)) : showroom K i m V= feeV (K.c m) i • dot_Q (hereV (K.c m) i):=by
 rcases i with _|⟨b,j,k⟩
 · change _= (1:ℂ) • _; rw [one_smul]; rfl
 let n:=K.c m; have h(j:mort x d):creation K j.1.val j.2.1 j.2.2 m V= Lifted.winding n j.1.val • put (hereF n j):=by unfold creation; rw [basisC,map_smul,Fock.create_put]; rfl
 have t(j:mort x d):removal K j.1.val j.2.1 j.2.2 m V= Lifted.winding n j.1.val • takeF (hereF n j):=by unfold removal; rw [basisC,Fock.remove,map_smul,Fock.create_put,star_smul,wind_realB]; rfl
 cases b<;> simp only [showroom,Option.elim_some,Bool.false_eq_true, ite_false, ite_true,Pi.mul_apply]; · rw [t, h, Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul]; rfl -- tune ambiguity
 rw [h,t,Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]; rfl
variable (F:Psu x d)
def showTop (F:Psu x d)(k:Side)(u:ℝ)(V:Pane k): FC (Single k):= if pingV x d u (onC k V) then marketD (pR k F) V else 0 -- for cost. ON only
lemma show_A (W:Pane n)(q:300<n.val)(d':d+6<n.val): showTop F n u W= if pingS u (knotX x d n) W then marketD (pR n F) W else 0:=by unfold showTop; rw [ping_W x d d'] -- prop-decidable
lemma show_V (K:Calibration)(m:Side)(V:Fields (K.c m))(u:ℝ): John F K u m V=showTop F (K.c m) u V.1:=by
 let n:=K.c m; let W:=onC n V.1; unfold John; rw [Finset.sum_apply,Finset.sum_apply]; unfold showTop; split;
 next p=>
    rw [pR,conn_X,Finset.sum_apply]; apply sum_congr rfl; intro i _; rw [Pi.mul_apply,Pi.mul_apply, show_t, publish]; unfold scalar glorified; rw [if_pos p, Algebra.smul_mul_assoc, one_mul,smul_smul,mul_comm (F i _)] -- tune
 next p=>
    apply sum_eq_zero; intro i _; simp only [Pi.mul_apply,scalar,glorified,if_neg p,zero_smul,zero_mul]
lemma boothQ {L: Paper n}(p:portable L)(g:Agora n)(V:Pane n): marketD L (GA g V)=twist (quantU (tradew n g)) (marketD L V):=by
 have he:=exportD (tradew n g) false false (αLines L V); rw [←p V g] at he; exact he.symm
lemma all_cov (m:Side)(K:Calibration)(u:ℝ)(v:portable (pR (K.c m) F)): Buffered.covariant (John F K u m):=by
 intro g V; rw [show_V,show_V]; unfold showTop; rw [pring,pring]; simp only [show (Buffered.simultaneous g V).1= GA g V.1 from rfl]; rw [show pingS u _ (GA g V.1) ↔_ from pingB V.1 g]; split; exact boothQ v g _; exact (map_zero _).symm
end ArtCart
end MastTin
end YM.CF.XGarden
end
