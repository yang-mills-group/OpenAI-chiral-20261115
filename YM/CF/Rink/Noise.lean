import YM.CF.Rink.Pear
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Rink
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
open Arena Tarn Reef
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
local notation "G"=> SU.group
variable {c f:Side}{S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{q:Chi}{s:Signed}{l n:ℕ}{x d β C D σ m:ℝ}{P:Tab S}{V:Config SU.group c}
variable {K:Teller G}
open AnalyticBridge.GaussianFieldAlignment Tensor Orthogonal PhysicalNext.OrderedAffine2B.SymRows Channels Locations
section
open AnalyticBridge.GaussianFieldAlignment Tensor Orthogonal PhysicalNext.OrderedAffine2B.SymRows Channels Locations Gauges
variable (s:Signed)(b:Site c)(A:Stores S)(U:Config G f)(V:Config G c)(k:S.Choices)(g:Site c→ SU.group.El)(h:S.patch.Branches S.kernel G) (q:Chi)(x w a:ℝ)
lemma knock{ι P:Type*}[DecidableEq ι][DecidableEq P](L:ι≃P)(Y X: Finset ι)(B:Finset P)(p:∀ i,i∈X↔ L i∈B): (¬ Disjoint Y X)↔ ¬Disjoint (Y.image L) B:=by
 rw [Finset.not_disjoint_iff,Finset.not_disjoint_iff]; constructor
 · rintro ⟨x,h,t⟩; exact ⟨_,mem_image_of_mem _ h,(p _).1 t⟩
 rintro ⟨x,h,t⟩; obtain ⟨k,u,rfl⟩:=mem_image.mp h; exact ⟨k,u,(p _).2 t⟩
local notation "t'"=>S.ratio.embed b
local notation "K₁"=>Locations.book s b A
local notation "v'"=>StepData.sendBonds s b
lemma on_p(i:Bond c): onS (K₁) x i↔ onS A x (v' i):=by
 unfold onS; rw [show pinPos (v' i)= (pinPos i).image _ from Locations.pin_map ..]; constructor
 · intro p y t; obtain ⟨j,v,rfl⟩:= mem_image.mp t; exact (dome_map ..).1 (p v)
 intro p y t; exact (dome_map ..).2 (p (mem_image_of_mem _ t))
lemma far_f(r:ℕ)(i:Cell f): i∈nearFace S ((K₁).dome r)↔ (shiftFaces s t' i)∈nearFace S (A.dome r):=by simp only [nearFace,mem_filter,mem_univ,true_and,start_map]; exact knock (StepData.sendSites s b) _ _ _ (fun _=>dome_map ..) -- tune ellipsis
lemma far_b(r:ℕ)(i:Bond c): i∈nearNoise ((K₁).dome r)↔ (v' i)∈nearNoise (A.dome r):=by
 change _ ↔ sendEdge s b i ∈ nearNoise _; simp only [nearNoise,mem_filter,mem_univ,true_and,pin_map]; exact knock (StepData.sendSites s b) _ _ _ (fun _=>dome_map ..)
lemma beam_v (i:Bond c)(z:Site f): z∈ beamV S i↔ affine s (S.ratio.embed b) z∈ beamV S (v' i):=by
 change _↔ _∈beamV _ (sendEdge s b i); have he(x y : Site f):separation (affine s (S.ratio.embed b) x) (affine s (S.ratio.embed b) y)= separation x y:=by simp [affine]
 simp only [beamV, pin_map, mem_biUnion,halo_spec]; constructor
 · rintro ⟨t,h,j,u,w⟩; exact ⟨_,mem_image_of_mem (affine s b) h, _,mem_singleton_self _,by rw [← he j z,mem_singleton.mp u,← Locations.affine_root] at w; exact w⟩
 rintro ⟨t,p,g,u,w⟩; obtain ⟨k,q,rfl⟩:=mem_image.mp p; rw [mem_singleton.mp u,Locations.affine_root,he] at w; exact ⟨_,q,_,mem_singleton_self _,w⟩
lemma near_u (i:Bond c)(j:Cell f): j∈nearT S i ↔ shiftFaces s (S.ratio.embed b) j∈ nearT S (v' i):=by
 simp only [nearT,mem_filter,mem_univ,true_and]; rw [show touched (shiftFaces s (S.ratio.embed b) j)=(touched j).image (affine s (S.ratio.embed b)) from Work.H03.touched_send ..,disjoint_comm, disjoint_comm (a:=beamV S (v' i))] -- tune picks
 exact knock (StepData.sendSites s (S.ratio.embed b)) _ _ _ (beam_v (S:=S) s b i)
local notation "Up"=> pull s t' U
local notation "Vp"=> pull s b V
local notation "P₁"=> Channels.ticket s b k
lemma rise_b(i:Cell f): Pressure.toll Up i=Pressure.toll U (shiftFaces s t' i):= Face.send_price U i s t' SU.group.chord SU.group.chord_inv (fun u v=> SU.group.chord_conj v u)
lemma mint_b{f': Side}(U:Config G f')(i:Cell f'): Pressure.toll (Reef.echo U) i=Pressure.toll U i:=by unfold Pressure.toll faceValue; rw [Reef.echo_t,Reef.cool]
include h
lemma roam_b(i:Bond c): wire (S.prediction Up P₁) Vp i= wire (S.prediction U k) V (v' i):=by
 rw [S.prediction_channel h]; unfold Channels.ticket; rw [Equiv.apply_symm_apply]; unfold wire; rw [Channels.read_back, Channels.read_back]; split
 · let Q:=S.prediction U k; let f:= V (v' i); let u:=Q (v' i); change SU.group.chord (f⁻¹*u⁻¹⁻¹)=SU.group.chord (f*u⁻¹); rw [← SU.group.chord_inv (f*u⁻¹),show (f*u⁻¹)⁻¹=f*(f⁻¹*u⁻¹⁻¹)*f⁻¹ by group,SU.group.chord_conj]
 rfl
section
omit h
abbrev quotaH(i:Bond c):ℝ:= if onS A x i then 1 else shutters q (a/2) (nearT S i) U -- order
lemma road(i:Bond c): Inure A x q k a i U= quotaH A U q x a i • SU.group.mat (S.prediction U k i):=by
 unfold Inure quotaH; split; · simp
 rfl
lemma costA(Y P: SU.group.El)(f:ℝ): fareG G (SU.group.mat Y * star (f • SU.group.mat P)) = 1+f*((1/2:ℝ)*SU.group.chord (Y*P⁻¹)^2-1):=by
 rw [star_smul, star_trivial, mul_smul_comm]; simp only [← SU.group.mat_inv,← SU.group.mat_mul]; let y:=Y*P⁻¹; have hp:=fare_h G y; unfold fareG at *; rw [map_smul,smul_eq_mul,Gauge.chord_price]; unfold y at hp; rw [←hp]; ring
lemma scale_t (i:Bond c):fareG G (SU.group.mat (V i)*star (Inure A x q k a i U))=1+quotaH A U q x a i*((1/2:ℝ)*(wire (S.prediction U k) V i)^2-1):=by rw [road]; apply costA
lemma quota_p (i:Bond c): quotaH (K₁) Up q x a i=quotaH A U q x a (v' i):=by unfold quotaH; apply if_congr (on_p s b A x _) rfl; exact prod_p (shiftFaces s t') _ _ (near_u (S:=S) s b i) _ _ fun i _=>congrArg (q.innerShare _) (rise_b (S:=S) s b U i)
end
lemma wing_t (i:Bond c): tidal (K₁) x w a q Up Vp P₁ i=tidal A x w a q U V k (v' i):=by
 unfold tidal; rw [scale_t,scale_t,roam_b s b U V k h,quota_p]; simp [Locations.book]
lemma gear_t(i:Bond c): tidal A x w a q (Lattice.gauge (constantGauge g S.ratio) U) (Lattice.gauge g V) k i= tidal A x w a q U V k i:=by
 let Z:=Lattice.gauge (constantGauge g S.ratio) U; have hh: quotaH A Z q x a i=quotaH A U q x a i:=by simp only [Z,quotaH,shutters,toll_gauge]
 unfold tidal; rw [scale_t,scale_t,hh,gust_p h,wire_gauge]
lemma echo_t(i:Bond c): tidal A x w a q (Reef.echo U) (Reef.echo V) k i=tidal A x w a q U V k i:=by
 have he: wire (S.prediction (Reef.echo U) k) (Reef.echo V) i=wire (S.prediction U k) V i:=by rw [(proceeds h U k).1]; unfold wire Reef.echo; rw [← map_inv, ← map_mul, Reef.cool]
 have hh: quotaH A (Reef.echo U) q x a i=quotaH A U q x a i:=by simp only [quotaH,shutters,mint_b]
 unfold tidal; rw [scale_t,scale_t,he,hh]
end
end YM.CF.Rink
