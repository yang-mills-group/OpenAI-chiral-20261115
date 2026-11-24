import GaugeFieldConstruction.Planetary
import GaugeFieldConstruction.Hab
import GaugeFieldConstruction.Virago
import GaugeFieldConstruction.Postmark
import GaugeFieldConstruction.Harries
set_option autoImplicit false
set_option maxHeartbeats 460000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus CF.Mint
namespace LocalLimit
open Preparation
open scoped ComplexOrder
variable {N:Side}{K : Teller SU.group}{R:Patch}{L:ChartRatio SU.group}
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
open YM.Gleam
open BProof.PricePort Gleam.clocks

namespace Papal
open scoped YM.CF.Mew
open Fock.Flux Girt TableF TableF.Lenten.Layout Gleam.Guide CF.XGarden CF.XGarden.MastTin ArtCart Zpress ScopeU Buffered
open FrameP
variable (s i k:ℕ)
namespace FrameP
open Buffered.Afterglow Journey Satin Tower SlabMark SlabMark.Etch
variable (H:Real.exp 1≤ P.x)
private abbrev castFe {n m:Side}(e:n=m)(T: Mark n):Mark m:=e ▸ T
abbrev filed (s i:ℕ)(F:Buffered.Family (tent Y H)):Mark (count Y s i) := send Y H i s (F (momentm Y i s)) -- height receipt
private lemma castFlip {n m:Side}(e:n=m)(F:Mark n)(i:Axis)(z:ℤ):castFe e (reflMark i z F)= reflMark i z (castFe e F):=by subst m;rfl
lemma fileMirror {F:Buffered.Family (tent Y H)} (b:Axis)(z:ℤ): filed Y H s i (Tower.mirror (tent Y H) b z F)=reflMark b z (filed Y H s i F):=
 castFlip (terrain Y H (Y.ir i) s) _ b z -- parameter order tune
private lemma castAr {n m:Side}(e:n=m) (F G:Mark n): castFe e (F+G)=castFe e F+castFe e G:=by subst m;rfl
private lemma castAb {n m:Side}(e:n=m) (F G:Mark n): castFe e (F*G)=castFe e F*castFe e G:=by subst m;rfl
lemma fileBoth {F G: Buffered.Family (tent Y H)} : filed Y H s i (F*G)=filed Y H s i F* filed Y H s i G:= castAb (terrain Y H (Y.ir i) s) _ _
lemma fileAnd {F G: Buffered.Family (tent Y H)} : filed Y H s i (F+G)=filed Y H s i F+ filed Y H s i G:= castAr (terrain Y H (Y.ir i) s) _ _
lemma fileW(z:ℂ)(F:Buffered.Family (tent Y H)) : filed Y H s i (z•F)= z • filed Y H s i F:=by
 have he{n m:Side}(e:n=m)(F:Mark n):castFe e (z• F)= z•castFe e F:=by subst m; rfl
 exact he (terrain Y H (Y.ir i) s) _
lemma fileSub {F G: Buffered.Family (tent Y H)} : filed Y H s i (F-G)=filed Y H s i F- filed Y H s i G:=by simpa [sub_eq_add_neg] using ((show _=filed Y H s i F+(-1:ℂ)• filed Y H s i G from (fileAnd Y s i H (F:=F) (G:=(-1:ℂ)• G)).trans (congrArg _ (fileW Y s i H (-1) G))))
lemma fileOne : filed Y H s i 1=1:=by
 have he{n m:Side}(e:n=m):castFe e 1= 1:=by subst m;rfl
 exact he (terrain Y H (Y.ir i) s)

local notation "fL"=> tent Y H
local notation "N'"=> count Y s i
variable {V G:Buffered.Family (tent Y H)}{m:ℕ}{x y:Cover}{S T:Finset Cover}{F f:Pane (count Y s i)→FC (Single (count Y s i))}{u z:ℂ}{B:Bool}
abbrev twistF {n:Side}(F:Pane n→ FC (Single n))(t z:ℂ): Mark n:= fun x=> 1+ z • (F x.1-t • 1)
structure PopArt (F f: Pane (count Y s i)→ FC (Single (count Y s i))) (V:Buffered.Family (tent Y H))(S T: Finset Cover)(u z:ℂ)(B:Bool)(m:ℕ) : Prop where
  generous : LongBand Y s i k F f (Satin.region S _) (Satin.region T _) B
  receipt : ∀ z:ℝ,Upright (count Y s i) (Satin.region S _) z m F → Upright (count Y s i) (Satin.region T _) z m f
  print : filed Y H s i V= twistF f (costχ B u) (costχ B z)
lemma WrapH {N:Side}(S:Finset Cover)(b:Axis)(d:ℤ): Satin.region (reflectedBox b d S) N=(Satin.region S N).image ((plane b d).anon N):=by
 unfold Satin.region reflectedBox; rw [image_image,image_image]; exact image_congr (fun i p=> (Shape.anno ..).symm)
lemma PopArt.mirrorH (Z:Kea.Pad P.K.j (count Y s i))(p:PopArt Y s i k H F f V S T u z B m)(b:Axis)(d:ℤ):
 PopArt Y s i k H F (spunA b d f) (Tower.mirror fL b d V) S (reflectedBox b d T) u z (!B) m:=by
 constructor
 · rw [WrapH]; exact BandMirror _ _ _ _ p.generous Z b d
 · rw [WrapH]; intro z h; exact UprightR (p.receipt z h) b d
 rw [fileMirror Y s i H b d,p.print]; funext x; unfold reflMark twistF; rw[theta_add,theta_smul,theta_sub, theta_one,theta_smul,theta_one,mixχ,mixχ]; rfl

lemma PopArt.dispatched (Z:Kea.Pad P.K.j (count Y s i))(p: PopArt Y s i k H F f V S T u z B m)(b:Axis)(v:ℤ) : ∃ (g: Pane (count Y s i)→ FC (Single (count Y s i))), PopArt Y s i k H F g (relocate fL b v V) S (plow fL b v T) u z B m:=by
 obtain H:= PopArt.mirrorH Y _ _ _ _ Z (PopArt.mirrorH Y _ _ _ _ Z p b 0) b (gaugeT fL v) -- tune
 rw [support_translation,sub_zero,Bool.not_not] at H; exact ⟨_, H⟩
lemma fullZone (Z:Kea.Pad P.K.j (count Y s i)){w:ℕ}{σ:Cover}(p:PopArt Y s i k H F f V S T u z B m)(q:Located (tent Y H) w σ V x G)(t:House (tent Y H) w σ 0 T): ∃ T:Finset Cover,∃ f: Pane (count Y s i) → FC (Single (count Y s i)), ∃ U:Bool, PopArt Y s i k H F f G S T u z U m ∧ House (tent Y H) w σ x T:=by
 induction q with
 | start=> exact ⟨T,f,B,p,t⟩
 | go i' v _ ih=> obtain ⟨T,f,U,k,h⟩:=ih; obtain ⟨l,g⟩:=PopArt.dispatched Y _ _ _ H Z k i' (w*v); exact ⟨_,l,U,g, House.go _ _ _ h i' v⟩
 | reflect i' v _ ih=> obtain ⟨T,f,U,k,h⟩:=ih; exact ⟨_,_,!U, PopArt.mirrorH Y _ _ _ H Z k i' _, h.reflect _ _ _ _ _⟩
lemma VPane (Z:Kea.Pad P.K.j (count Y s i)){w r n:ℕ}{σ l' h':Cover}(p:PopArt Y s i k H F f V S T u z B m)(q:SlabMark.Etch.Panel (tent Y H) w σ V l' h' n G)(t:House (tent Y H) w σ 0 T)(a:Proscenium (tent Y H).B w (count Y s i) r)(hp:Hall r l' h'):
 ∃ (l:List Cover), l.Nodup ∧ l.length=n ∧ ∃ (A:Cover→ Pane (count Y s i) → FC (Single (count Y s i)))(T:Cover → Finset Cover)(b:Cover→Bool),
 Set.PairwiseDisjoint ↑l.toFinset (fun i' => Satin.region (T i') (count Y s i)) ∧ (∀ v∈l,∃ G',PopArt Y s i k H F (A v) G' S (T v) u z (b v) m) ∧ sharp Y H s i k G=graphicMode Y s i k (ShootF l (fun i=>costχ (b i) z) (fun i=>costχ (b i) u) A):=by
 obtain ⟨L,rfl,h,x,rfl⟩:=q; let l:= L.map Prod.fst; have hx:l.Nodup:=List.pairwise_map.mpr x
 have g(A)(v:A∈L):= fullZone Y s i k H Z p (h A v).2 t
 choose T f b P0 V' using g
 -- use global extension from x Nd. list Finset T.
 have he(u:Cover)(p:u∈ l): ∃ z, z∈L∧ z.1=u:= List.mem_map.mp p
 let F'(u:Cover)(p:u∈l):= (he u p).choose
 let T'(u:Cover):Finset Cover:= if p:u∈ l then T (F' u p) (he u p).choose_spec.1 else ∅
 let A'(u:Cover):Pane N'→ FC (Single N'):= if p:u∈ l then f (F' u p) (he u p).choose_spec.1 else 0
 let b'(u:Cover): Bool:= if p:u∈ l then b (F' u p) (he u p).choose_spec.1 else false
 have ht(x':Grain (tent Y H))(v:x'∈L): T' x'.1=T x' v ∧ A' x'.1=f x' v∧ b' x'.1=b x' v:=by
    have e':x'.1∈l:=List.mem_map_of_mem v
    let h:=F' x'.1 e'; have hz : h.1=x'.1:= (he x'.1 e').choose_spec.2
    have w: h=x':= List.inj_on_of_nodup_map hx (he x'.1 e').choose_spec.1 v hz -- tune via nodup.map helper
    dsimp only [T',A',b']; simp only [dif_pos e']
    exact ⟨by congr,by congr,by congr⟩
 refine ⟨l,hx,List.length_map ..,A',T',b', ?_, ?_,?_⟩
 · intro x px y py g'
   change Disjoint (Satin.region (T' x) _) (Satin.region (T' y) _)
   obtain ⟨xc,hx,rfl⟩:= he x (List.mem_toFinset.mp px); obtain ⟨yc,hy,rfl⟩:= he y (List.mem_toFinset.mp py)
   rw [(ht _ hx).1,(ht _ hy).1]; exact a.disjoint hp (h _ hx).1 (h _ hy).1 g' (V' _ hx) (V' _ hy)
 · intro g w; obtain ⟨a,u,rfl⟩:= he g w
   rw[(ht _ u).1,(ht _ u).2.1,(ht _ u).2.2]; exact ⟨_, P0 _ u⟩
 let Ξ (l:List Cover):= ShootF l (fun i=>costχ (b' i) z) (fun i=>costχ (b' i) u) A'
 have he(X: List (Grain (tent Y H)))(w:X⊆ L): filed Y H s i (castings (tent Y H) X)=(fun y=> Ξ (X.map Prod.fst) y.1):=by
    induction X with
    | nil=> exact fileOne Y s i H
    | cons X l ih=>
       have hx:= w List.mem_cons_self; let K:= List.map Prod.fst l
       let T:= A' X.1; have hT:filed Y H s i X.2= twistF T (costχ (b' X.1) u) (costχ (b' X.1) z):=by unfold T; rw [(ht _ hx).2.1,(ht _ hx).2.2]; exact (P0 _ hx).print
       rw [show castings _ (X::l)= X.2*castings (tent Y H) l from rfl,fileBoth Y s i H,hT,ih (fun i v=>w (List.mem_cons_of_mem _ v))]; rfl
 change Journey.compass _ _ _ _ (filed _ _ _ _ _)=_; rw [he L (fun _ p=>p),twin_p]

lemma NovelGreen (N:Side)(w:300<N.val)(d:ℕ)(r:ℝ)(g:0≤r)(Q:LocalLimit.Badge)(Nheat:ℕ)(u: TintDemand)(Pz: LicensedHeight (tagged_B Q) Nheat u P)(C:ℝ→ℝ){f:ℝ}(j: RunRate 0 f C) : ∀ᶠ s in atTop,let x:= hat P.R.L P.x s
 ∀ i k:ℕ,∀ ℓ:s ≤ Y.uv k,(Y.voyage i).kick ≤ k→ ∀ (b K:ℕ)(σ:Cover), Proscenium (tent Y H).B b (count Y s i) K → (SlabMark.Etch.ratio (tent Y H).B b:ℝ)≤ C x→ ∀ (M:Male)(p:BudgetPoint),p.order ≤6→ p.power ≤3→ p.threshold=(gram Y s i k).p.threshold → ∀ (A:List AdmitA)(S:Finset Cover)(z:ℂ), ReaderShip _ A d r (Satin.region S (count Y s i)) → ‖z‖≤KeyTurn x→ ∀ (j:Axis)(k':ℤ), House fL b σ 0 (plow fL j k' S) →∀ V:Buffered.Family (tent Y H),filed Y H s i V=twistF (Uranus Y s i k N A p M) (allotΩ Y s i k (headPlus Y s i N A p M) ℓ) z → SlabMark.Etch.Mosaic b σ K (relocate fL j k' V) (Real.exp (KeyTurn x*ClockTurn x)) (Journey.sharp Y H s i k):=by
 obtain ⟨Hv,B,E⟩:=paid_inches Pz
 obtain ⟨W,J,L,K⟩:=HeraldReader Y N w d r g Hv
 obtain ⟨BR,BT,β,hκ,pκ,Hκ⟩:= exhib_T Y Hv _ one_pos
 filter_upwards [K,Hκ, Emergence Y B E Hv (2*d) W C J j L] with s q H p
 intro X i k ℓ v b U σ a c M p' p₀ p₁ p₂ A S z r' c' j' s' Z F e l' H' n v₀ v₁ G v₂
 let U':=Uranus Y s i k N A p' M
 have hv:PopArt Y s i k _ U' U' F S S _ z false (2*d):= ⟨BandStart _ _ _ _, fun _ z=>z,e⟩
 obtain ⟨f',he⟩:=PopArt.dispatched Y s i k _ (H _ _ ℓ).1 hv j' s'
 obtain ⟨l₁,hz,hf,Yb,S',h,Sp,pG,P₁⟩:=VPane Y _ _ _ _ (H _ _ ℓ).1 he v₂ Z a v₁
 let f'(w:Cover):=costχ (h w) z; let B:= allotΩ Y s i k (headPlus Y s i N A p' M) ℓ; let R(v:Cover):=costχ (h v) B
 have H':sites (count Y s i)≤ C X*l₁.length:=by
    apply le_trans _ (mul_le_mul_of_nonneg_right c (by positivity)); rw [hf]; refine ?_
    have he:= a.density v₀
    unfold Py.Rate.sites; exact_mod_cast he
 rw[P₁,←hf,←Real.exp_nat_mul,mul_comm _ (KeyTurn X*ClockTurn X)]
 refine p i k ℓ v Cover (Yb) R (fun i' => Satin.region (S' i') _) l₁ hz Sp ?_ H' f' (fun i _=> (norm_cχ _ _).trans_le c')
 intro j v; obtain ⟨V,p⟩:=pG j v
 exact q _ _ ℓ M p' p₀ p₁ p₂ _ _ r' _ _ _ p.generous p.receipt
#print axioms NovelGreen
end FrameP
end Papal
end LocalLimit
end Rate
end YM.CF.Py
end
