import YM.CF.BProof.Start.House
import YM.CF.BProof.Gates.Side

set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Start
open Function Filter MeasureTheory Finset
open Lattice Tenant Lat Cube Skye RG Angular Wilson Rhythm Hero Mark Branch
open scoped Topology BigOperators Classical
open Gates Gates.Stage Gates.Stage.Setup Mapping House
open Stint Tape Hearth Prime Estate Cliff
open Jet Paige Drapes Vault Oasis Bias Weights Cabinet Mint Contour
variable {N:Side}{d K:ℕ}{c:Clip}{w R v:ℝ}(S:Gates.Stage c w R v)
variable {m m' L B:Side}{j:ℕ}{a b l r:ℝ}{D:Spin.Ready j a b l r}{u:ℝ}(E:Essence D u)
variable {rₜ a':ℕ}(Δ: Rhythm.Note E (gap L a') rₜ)
variable {p:Odd L.val} {Y:Pricing j L p (Vault.Thread j)} {δ:ℝ}{F:Grasp Y B δ}
variable {E Δ S}{U H:ℝ} (J:Mote S E Δ F U H)
open Veil Anthem
-- geometry lower & divisibility. tall for any additional restrictions (≥4 radii for N frames). Use only licence yields gap layout all matching. Extra Borel winding fits. 
namespace Mote
open Seam Trek Contour Contour.Tower
variable {ν h:ℝ} (y:ℝ)(W:ℕ)
structure Extent (N:Side):Prop where
 stamp : Tori S L y W (More N)
 lens : E.H.body.val∣ (More N).val
 port : 4 ≤ (More N).val/E.H.body.val
 book : E.H.whole.val∣ (More N).val
 care : 4≤ (More N).val/E.H.whole.val
 giant : E.pre.size≤ N.val
 near : J.k ≤ N.val
variable {B':ℝ→ℕ}{Fp:ℝ→ℝ} (Γ: J.Licence B' Fp W y h)
variable {y W}
-- options can take extra costs e.g. distance powers w0 on sewn. J.k threshold fixed. Demand floor. Include F.Grasp sizes later.
include Γ
lemma powers : ∃ A:ℕ,0<A∧ ∀ N:Side,A∣ N.val → Extent J y W N :=by
 let P:=Γ.baseL; let q:=4*Gates.Stage.require S L y W; let s':= E.H.body; let v':= E.H.whole; have hc:0<W:=  lt_of_lt_of_le (Gates.least_p ..) P.choice
 have ht:0<q:= by unfold q Gates.Stage.require; have J:= win_pos L y; have p:=Gates.PP L y; have h:=posF y S.scene.size; positivity
 let u:= E.pre.size+J.k+1; have hu:0<u:=by positivity
 let A:=q*(4*s'.val)*(4*v'.val)*u; refine ⟨A,(by unfold A; positivity),fun N p=>?_⟩
 have hz (x: Side)(g:4*x.val∣ A): x.val ∣ (More N).val ∧ 4 ≤ (More N).val/x.val:=by
    have ht:4*x.val∣ (More N).val:= dvd_mul_of_dvd_left (dvd_trans g p) 2
    exact ⟨dvd_trans (dvd_mul_left ..) ht,(Nat.le_div_iff_mul_le x.property).2 (Nat.le_of_dvd (More N).property ht)⟩
 obtain ⟨h1,h2⟩:= hz s' (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left ..) _) _); obtain ⟨h3,h4⟩:=hz v' (dvd_mul_of_dvd_left (dvd_mul_left ..) _); have hv:u≤N.val:=Nat.le_of_dvd N.property (dvd_trans (dvd_mul_left ..) p);
 refine ⟨ ?_,h1,h2,h3,h4,(by unfold u at hv; omega),(by unfold u at hv; omega)⟩; exact Gates.Stage.layout S L a' y W P (More N) (dvd_mul_of_dvd_left (dvd_trans (show q∣A from dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right ..) _) _) p) 2)
omit Γ
private lemma appoint (m N:Side)(h:m.val∣N.val)(v:4≤N.val/m.val): ∃ k:Side,∃ t:Ratio k N, t.count=m∧4≤k.val:= ⟨⟨N.val/m.val,by omega⟩,⟨m,(Nat.div_mul_cancel h).symm⟩,rfl,v⟩
-- licences stats school ingredients. keep width
variable {N:Side}(P:J.Extent y W N)
variable (V:Setup S L a' (More N) W y)
variable (T:PathData SU.group)(U₀:Orbit N→Pane N)(θ:ℝ)
include Γ P
lemma Grade (hz:2*L.val∣a'): Nonempty (Setup S L a' (More N) W y):= qualify S L (More N) a' y W Γ.baseL P.stamp hz
lemma studies (δT:δ≤ E.pre.limit)(cH:δ≤E.H.calm)(hp:0≤δ) (u:T.Bounds c w R v)(p:θ∈ Set.Icc (1/2) 2)(v:thresh y≤ν)(hv:Roof N ν δ rₜ U₀) : Nonempty (School V T θ E Δ U₀ ν δ 200):=by
 let W':= Γ.routeL; obtain ⟨k,f,h1,h2⟩:= appoint _ _ P.lens P.port; obtain ⟨n,p',h3,h4⟩:= appoint _ _ P.book P.care; let e:SiteUp V E.H Δ.clock 200:= ⟨(Instructions E Γ.baseL V Δ W').1,(by unfold Deep.D; rw [V.length Γ.baseL]; exact Γ.roof),(by rw [V.space]; exact Γ.cap),le_rfl⟩
 exact ⟨δT,P.giant,W',e,⟨u,p,hv,v,Δ.postL,hp,cH⟩, k,n,f,h1,p',h3,h2,h4⟩
omit P
variable (Z:School V T θ E Δ U₀ ν δ 200)
lemma clock_Z : Clock Z J.k (J.sizeC y):=by
 let P:= Γ.baseL; have hv:=Γ.clock; have e:= V.length P; have he:Z.μwage=Mote.μ (Δ:=Δ):= Z.silhouette_p P -- tune unused P?
 refine ⟨J.paid,J.pos,(by rw [Deep.D,e,he]; omega), (by rw [V.space,he]; exact Γ.roomV)⟩
lemma solid : Pods.Brick.Solid y V.yard.short V.g.count.val:= by rw [V.width,V.space]; exact Γ.solidL
lemma tag_Z : (J.mode y W).Buy quotaχ (meters W) V.g.count.val V.yard.short y:= by rw [V.space,V.width]; exact Γ.tagL
end Mote
end YM.CF.BProof.Start
