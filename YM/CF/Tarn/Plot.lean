import YM.CF.Tarn.Vase
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Tarn
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace Matrix Kronecker
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
open Arena
local notation "G"=> SU.group
variable {c f:Side}{S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{q:Chi}{s:Signed}{l n:ℕ}{x d β C D σ m:ℝ}{P:Tab S}{V:Config SU.group c}
open Cube
variable {r:ℕ}{u v W a b w s':ℝ}{i:Site c}{F:Tab S}{K:Teller G}{P': Tab S}
lemma bench (s:Signed)(b:Site c)(P:Tab S)(V:Config G c):clue S s b (bunk S P V)=bunk S (dial S s b P) (pull s b V):=by
 let M:=bunk S P V; let A:=clue S s b M; have ht:A.U=1:=by unfold A clue pull; funext k; simp only [Step.read]; split; change (1:SU.group.El)⁻¹ =1; simp; rfl
 have hv:A.key=bareStores S:=by change AnalyticBridge.GaussianFieldAlignment.Locations.book s b (bareStores S)= _; simp [AnalyticBridge.GaussianFieldAlignment.Locations.book,bareStores]
 have hz:A.z=0:=map_zero _; change A=bunk _ _ _; refine (show A={A with U:=1,z:=0,key:=bareStores S} from ?_); conv_lhs => rw [show A= ⟨A.key,A.park,A.k,A.V,A.U,A.z⟩ from rfl]; skip
 rw [show ({ A with U:=1,z:=0,key:=bareStores S} : Monk G S)=⟨bareStores S,A.park,A.k,A.V,1,0⟩ from rfl,hv,hz,ht]
section
variable(T:Tube G S)(x u:ℝ)(q:Chi)(d:ℝ)(l:ℕ)(K:Teller G)(h:K.Funds S T)(p:Ready T x)(hp:0 < m)(he:1000 ≤ radiusB x)
 (H:∀ (V:Tab S)(y:Mast G c), ‖y‖<1→ FreeResolvent.Gap (baseX T x (bareStores S) V.1 V.2 (satU G u y)) m)
lemma transT(c:Side)(y:Site c)(u:ℝ){V:Config G c}(h:V∈pines G c u):Lattice.translate y V∈pines G c u:=by
 obtain ⟨v,hv,rfl⟩:=h; let k(i:Body 1 c):=(i.1+y,i.2); let r:Mast G c:=fun i=>v (k i.1,i.2)
 refine ⟨r,mem_ball_zero_iff.mpr (lt_of_le_of_lt ?_ (mem_ball_zero_iff.mp hv)),?_⟩
 · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i=>norm_le_pi_norm v _
 funext b; change represent (tint G (Body 1 c) (u • r)) b=represent (tint G (Body 1 c) (u • v)) (b.1+y,b.2); rw [Work.F03.represent_link, Work.F03.represent_link]; apply congrArg SU.group.lieExp; ext; rfl
lemma pivotU (c:Side)(b:Site c)(r:ℕ)(P V:Config G c)(i:Site c)(h:drift G (i+b) r P V):drift G i r (Lattice.translate b P) (Lattice.translate b V):=fun e t=> h (e.1+b,e.2) (by simpa [separation] using t)
lemma trop(g:Site c→SU.group.El)(b:Site c)(V:Config G c): Lattice.translate b (Lattice.gauge g V)= Lattice.gauge (fun i=>g (i+b)) (Lattice.translate b V):=by
 ext1 v; change _*_* (g _ )⁻¹=_*_* (g _)⁻¹; simp only [←add_assoc,add_right_comm _ b (step v.2)]; rfl -- tune
lemma paveT {V:Config G c}(i b: Site c)(h:found (pines G c u) (i+b) r V):found (pines G c u) i r (Lattice.translate b V):=by
 obtain ⟨g,U,hp,t⟩:=h; exact ⟨fun y=>g (y+b), Lattice.translate b U, transT _ _ _ hp, (trop ..) ▸ pivotU _ _ _ _ _ _ t⟩
lemma coldPull(V:Config G c)(g:Signed)(b:Site c):pull g b (1:Config G c)=1:= by funext i; unfold pull Step.read; split; change (1:SU.group.El)⁻¹=1; simp; rfl
include H h he hp
lemma pest(P:Tab S)(V:Config G c)(i b: Site c)(s:Signed)(hv:V∈pines G c u):zestQ T x q d l P (affine s b i) V=zestQ T x q d l (dial S s b P) i (pull s b V):=by
 obtain ⟨y,hv,rfl⟩:=hv
 have ht(y:Mast G c)(p:‖y‖<1) := turnQuill T x q d l (bunk S P (satU G u y)) h s b (H P y p) hp (by omega) i; have hρ:=ht y (mem_ball_zero_iff.mp hv); have he:=ht 0 (by simp); rw [bench] at he hρ; rw [show satU G u (0:Mast G c)=1 from (by simp [satU,facadeX]),coldPull (satU G u y)] at he; exact congrArg₂ (·-·) hρ.symm he.symm
include p
lemma neck (i b:Site c)(V:Config G c): neatQ T x u q d l P (i+b) V=neatQ T x u q d l (dial S 1 b P) i (Lattice.translate b V):=by
 let X:=pines G c u; let r:=(l+68)*radiusB x
 have hx: affine 1 b i=i+b:=by simp [affine]
 by_cases hv:found X (i+b) r V
 · obtain ⟨g,U,h',t⟩:=hv
   unfold neatQ; rw [land_s (zStamp _ _ _ _ _ _ (H P) h hp p he) h' _ t]; let P':=dial S 1 b P; rw [land_s (zStamp _ _ _ _ _ _ (H P') h hp p he) (transT c b u h') _ (show drift G i r (Lattice.gauge (fun i=>g (i+b)) (Lattice.translate b U)) (Lattice.translate b V) from trop g b U ▸ pivotU _ _ _ _ _ _ t),←hx -- fix
      ,pest T x u q d l K h hp he H P U i b 1 h',pull_one] -- order
 have hh:¬found X i r (Lattice.translate b V):= fun p=>by
    have hp:i=(i+b)+ -b:= by simp
    have hz:=paveT (r:=r) u (i+b) (-b) (hp ▸ p)
    rw [show Lattice.translate (-b) (Lattice.translate b V)=V from (by ext1 x; change V (x.1+ -b+b,x.2)=_; simp)] at hz; exact hv hz
 unfold X r at hv hh
 simp only [neatQ,salsa,dif_neg hv,dif_neg hh]
end
end YM.CF.Tarn
