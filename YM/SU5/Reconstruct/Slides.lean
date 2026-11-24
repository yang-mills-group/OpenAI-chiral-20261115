import YM.SU5.Reconstruct.Base
set_option autoImplicit false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 470000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
open Tapestry Tapestry.Altitude PhaseChoice
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
open Tower.Selected Set MeshClock Tapestry.Exhibition
open SelectionAnalysis Vacancy.Average
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
  {L:Rack Λ l}{B:Clay Λ l}{T:ℕ→ℕ→Tariff}{t:ℕ→Tariff}(D:Fashion Y H i k I E L B T t)
  (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
local notation "Dₚ" => D.toExhibition
local notation "V" => D.univ_
local notation "Q" => G.history
local notation "Qt" => G.clipped
local notation "χ" => Dome (tent Y H)
local notation "O" => Altitude.Cloud (Dome (tent Y H))
local notation "P₀" s:max => vistaFinish Y H s (Dₚ)

section here
variable (C : ∀ i: Axis, Tower.Arena Y H G.history.circuit i 0 false)
variable (c: (displayAlgebra Y H D.univ_ G.history G.clipped 0 false (C 0)) →⋆ₐ[ℂ] ℂ)
variable {s:ℕ}{j:Axis}{σ:Type} {U:σ→ Set RSpace}{x:∀ i,Pol Y H (U i)}
variable (F:Board Y H D s j U x)
local notation "M"=> timeMesh Λ
local notation "Rr" i:max=> inAxis Y H D G C c i
local notation "L₀" i:max => indoor Y H V Q Qt i false (C i) (Rr i)
local notation "Op" a:max => procession Y H V Q Qt j false (C j) (Rr j) a
local notation "p₀" i:max=> doorstep Y H V Q Qt i false (C i) (Rr i)
open StripCard
local notation "ζ₀" i:max z:max=> atEstate Y H V Q Qt i false (C i) (Rr i) z
local notation "B₀"=>hallCall Y H D G C F
local notation "μ"=>physPos Λ
local notation "pF"=>navFilm Y H D G C c F
local notation "m₀"=>meshPos Λ s
local notation "Z₀"=> Marks (tent Y H) false
local notation "η₀" v:max=> relocateWorld Y H false v
-- chosen axis stamps. Focally coordinates borrowed from `concert` coworkers
variable (p:σ → Cover)(Z:List σ)
local notation "qh" s:max x:max p:max=> entrance Y H V s Q Qt j false (C j) x p
local notation "Υ" p:max=>procession Y H V Q Qt j false (C j) (Rr j) p
local notation "Gq" p:max => bud Y H V s Q Qt j false (C j) (Rr j) p
local notation "ι" x:max => futureMark Y H s j false x
local notation "Ft"=> Tower.Field Y H s j 0 false
lemma hallAct (i:σ)(u:Tower.Field Y H s j 0 false):
    (procession Y H V Q Qt j false (C j) (Rr j) (B₀ i)) (bud Y H V s Q Qt j false (C j) (Rr j) u)=
      bud Y H V s Q Qt j false (C j) (Rr j) (slabT Y H s j false (F i).span (composer Y H s j (F i).cargo) u):=by
 obtain ⟨w,k,v,rfl⟩:= artist_fits_slab Y H s j false u
 unfold hallCall; let y:= (F i).cargo; let x:= composer Y H s j y
 let a:= (F i).paidH
 rw [turns Y H V s Q Qt j false (C j) _ v k,arrive_mul,entrance_pair]
 have h:= turns Y H V s Q Qt j false (C j) (Rr j) (edit Y H s j false _ w x v) (Nat.add_pos_left a _); exact h.symm
lemma sees (i:σ) : futureMark Y H s j false (composer Y H s j (F i).cargo).val = relocateWorld Y H false (-(F i).origin_) (fieldArg Y H (vistaFinish Y H s D.toExhibition (x i).val)):=
  Eq.trans (Subtype.ext (F i).points : (ι (composer Y H s j (F i).cargo).val)=fieldArg Y H (march Y H (-(F i).origin_) ((P₀ s) (x i).val))) (marchOut Y H _)

-- suffix label relative to prior cutoff (prior=end of previous entry when ascending). AnchorE
-- expression is at fully supported height s. Movement compares to exact Sch.
local notation "d̂" i:max=> (F i).origin_+p i
local notation "fP" i:max=> fieldArg Y H ((P₀ s) (x i).val)
local notation "f₁" i:max=> fromBase Y H D (F i)
local notation "ẑ"=> fun i=>meshPos Λ s (p i)
-- previous ticket horizon
noncomputable def callLedger (u:Cover) := (Z.map fun i=> relocateWorld Y H false (p i-u) (fieldArg Y H (vistaFinish Y H s D.toExhibition (x i).val))).prod -- D yes; implicit f not using F!! signature implicit annoying
local notation "ℒ" z:max u:max=> (List.map (fun i=> relocateWorld Y H false (p i-u) (fieldArg Y H ((P₀ s) (x i).val))) z).prod
lemma ledger_shunt (t:Cover)(d:Cover): (η₀ d) (ℒ Z t)=ℒ Z (t-d):=by
 rw [world_prod,List.map_map]
 have he: (η₀ d) ∘ (fun i=> (η₀ (p i-t)) (fP i))=fun i=> (η₀ (p i-(t-d))) (fP i):= funext fun i=>by rw [Function.comp_apply,world_held,show d+(p i-t)=p i-(t-d) from by abel]
 rw [he]
lemma studio (u:Cover)(t:OfferedOn Y H D Z F (fun i=> (μ (meshPos Λ s (p i))))) (a:∀ i∈Z,u j ≤ ((d̂ i):Cover) j) :
    ∃ x': Tower.Field Y H s j 0 false,pF ẑ Z (meshPos Λ s u)=bud Y H V s Q Qt j false (C j) (Rr j) x' ∧ (ι x')=ℒ Z u:= by
 induction Z generalizing u with
 | nil => exact ⟨_, (Tower.Selected.root Y H V s Q Qt j false (C j) _).symm,rfl⟩
 | cons i z ih =>
   obtain ⟨g,e⟩:= List.pairwise_cons.mp t
   let y: Cover:=d̂ i
   let w:Cover:= lastBit Y H D (F i)
   have h : ∀ k∈z, (y+w) j ≤ ((d̂ k):Cover) j:=by
     intro k ht
     have he: ∀ (k:σ), (μ (meshPos Λ s (d̂ k)))=StripCard.starts Y H D (F k) ((μ ((ẑ) k))):=fun k=>by unfold StripCard.starts fromBase; rw [map_add,map_add]
     apply (bell_le M _ _ _).1
     change (μ (meshPos Λ s (y+w))) j≤ (μ (meshPos Λ s (d̂ k))) j
     have hp: (μ (meshPos Λ s (y+w)))=StripCard.ends Y H D (F i) (μ ((ẑ) i)):=by rw [map_add,map_add]; unfold y; rw [he i]; unfold StripCard.ends finishBit StripCard.starts; rw [map_add]; change _=(μ (f₁ i)+μ (meshPos Λ s w))+ _; abel
     rw [hp,he k]; exact (g k ht).le
   obtain ⟨v,r,q⟩:= ih _ e h
   let X:=composer Y H s j (F i).cargo
   let x':Ft:= slabT Y H s j false _ X v
   let d:=y-u
   have he:0 ≤ d j:= sub_nonneg.mpr (a i (by simp))
   let n:=(d j).toNat
   let f:= tick Y H s j 0 false (2*n) (Vacancy.transport Y H s j false (look j) (fun k=> d k.val) x')
   refine ⟨f,?_,?_⟩
   · unfold navFilm; rw [film_step];
     have hr: bottomPlay Y H D F i+ widthPlaying Y H D F i + meshPos Λ s (p i)= (meshPos Λ s (y+w)):=by rw [map_add]; unfold y; rw [map_add]; unfold bottomPlay widthPlaying StripCard.fromBase StripCard.breadthOn; unfold w; abel
     have hz: (parkFilm (bottomPlay Y H D F) _ _ _ _ _ z (meshPos Λ s (y+w)):L₀ j)= Gq v:=r
     rw [hr,hz,hallAct Y H D G C c F]
     change (ζ₀ j ((f₁ i)+ (meshPos Λ s (p i))- (m₀ u))) (Gq x') = Gq f
     rw [show (f₁ i)+(meshPos Λ s (p i))-m₀ u=m₀ d from ?_]
     · exact apt_rides Y H V s Q Qt j false (C j) (Rr j) x' d n (Int.toNat_of_nonneg he)
     unfold fromBase d y; rw [map_sub, map_add]
   have hw:w=((F i).span:ℤ) • step j:=by unfold w lastBit; simp
   have hb:(ι x')=(ι X.val)*(η₀ w) (ι v):=by
     rw [hw,cad_one_by]; apply Subtype.ext; exact slab_eq Y H s j false (F i).span X v
   have hy (F G:Z₀): (η₀ d) (F*G)= (η₀ d) F*(η₀ d) G:=by simpa only [List.prod_cons,List.prod_nil,List.map_cons,List.map_nil,mul_one] using world_prod Y H d [F,G]
   have hv:d + -(F i).origin_=p i-u:= by unfold d y; abel
   rw [show (ι f)=(η₀ d) (ι x') from aptMoves Y H V s Q j false (C j) x' d n (Int.toNat_of_nonneg he),hb,hy,world_held]; unfold X; rw [sees,world_held,hv,q]
   simp only [List.map_cons,List.prod_cons]; rw [ledger_shunt Y H D p z ((y+w):Cover) (d+w) (x:=x) (s:=s),show y+w-(d+w)=u by unfold d; abel] -- implicit params?

lemma earliest {σ:Type}(f:σ→ℤ)(z:List σ):∃ x:ℤ,∀ i∈z,x ≤ f i:=by
 induction z with | nil=>exact ⟨0,by simp⟩ | cons i z ih=> obtain ⟨x,h⟩:= ih; exact ⟨min (f i) x,by simpa [min_le_left] using (fun k p=>le_trans (min_le_right (f i) _) (h k p))⟩ -- simp for forall
set_option maxHeartbeats 260000 in
lemma paid_update (v':placement Λ)(t:OfferedOn Y H D Z F (fun i=> (μ ((ẑ) i)))):
    inner ℂ (p₀ j) (pF ẑ Z v')=poseValue Y H D G C c U x Z ẑ := by
 obtain ⟨b,p'⟩:= earliest (fun i=> (p i+(F i).origin_) j) Z
 let u:Cover:= fun _=> b
 have he : ∀ i∈Z,u j ≤ ((d̂ i):Cover) j:=by intro i h; rw [add_comm (F i).origin_]; exact p' i h
 obtain ⟨x',p'',q⟩:= studio Y H D G C c F p Z u t he
 rw [nav_before Y H D G C c F ẑ Z v' (m₀ u),p'',call]; rw [q]; rw [← world_still Y H V s Q Qt j false (C j) (Rr j) u (ℒ Z u), ledger_shunt Y H D (x:=x) (s:=s) p Z u u,sub_self]; simp_rw [sub_zero]; exact (poses_read Y H D G C c U x ẑ Z j (OfferedOn_apart Y H D Z F _ t) s p (fun i=>rfl) (fun i=>(F i).prepared)).symm
set_option maxHeartbeats 240000 in
lemma frame_update [Fintype σ] (v w) (t:OfferedOn Y H D Z F (fun i=> physPos Λ (v i))): inner ℂ (p₀ j) (pF v Z w)=poseValue Y H D G C c U x Z v:=by
 obtain ⟨n,Ht,P⟩:= ((eventually_ge_atTop s).and (Filter.eventually_all.mpr (fun i=>contHeight (v i)))).exists
 choose p h using P
 let F':= finer Y H D G F n Ht
 rw [← nav_higher Y H D G C c F v _ Ht]; rw [←funext h] at t ⊢; exact paid_update Y H D G C c F' p Z w ((OfferedOn_finer Y H D G Z F _ _ Ht).2 t)
end here
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
