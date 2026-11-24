import YM.SU5.Registration.Rasp.Sponsor
/-!
  # The Euclidean, late-consultation fields over our M4 map
  Unprojected ColorHil -> G uses coherence of this same elected character. G
  has powers w.r.t. actual physical clock, not arbitrary GNS Hilbert built per axis.
  Work with WPermit estimates on ANY stamped family with coefficients at its
  native printed height. Use to compute Schwinger prices and ordered transfer.
  Projection in pricing sharp readings from G is only qualified where authorized
  (`Ellis` & all-coordinate separations etc.).
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set
open SatinRegistration
namespace Spine
variable (P:Spine)
-- geometry ANY axes
local notation "Χ"=>P.Spectrum0
local notation "Θ"=>P.advocate 3
local notation "E₀"=>P.ColorHil
local notation "H₀"=>P.ManyF
local notation "qz"=>P.wealth
local notation "S₀"=>P.seasons
variable (x:P.Spectrum0 3)(a:Axis)
local notation "ξ"=>Θ x a
local notation "S"=>(P.seasons a (P.advocate 3 x a))
local notation "H"=>(P.ColorHil a (P.advocate 3 x a))
local notation "G"=>(P.ManyF a (P.advocate 3 x a))
local notation "pc"=>P.cartage a (P.advocate 3 x a)
local notation "T₀"=> (S).E
local notation "Ω"=> P.heaven a ξ
local notation "T"=> timeMesh P.par
open Swatch
local notation "τ" p:max=> Real.toNNReal (p:ℝ)
local notation "GOp" x:max=> (P.ManyF a (P.advocate 3 x a)).Op
local notation "Θ'" x:max=> P.seasons a (P.advocate 3 x a)
local notation "Φ"=>P.Spectrum0 3
open Swatch
variable {I:Type*}(L:List I) [DecidableEq I]
section single
variable (A:I→P.Swatch) (T':∀ i,P.Commission a (A i))
local notation "!Z~"=> fun (i:I)=> (T' i).all -- no implicit V I at funext.
abbrev all_desk : Prop:= ∀ i,P.Commission a (A i)
lemma all_desk_update (h:P.all_desk a A)(i:I)(B:P.Swatch)(v:P.Commission a B) : P.all_desk a (Function.update A i B):=by
 intro k; by_cases hz:k=i
 · subst k; rwa [Function.update_self]
 rw [Function.update_of_ne hz]; exact h k
-- passports requested at ALL generic configurations (perm anywhere for other axes)
def Paper (A:I→P.Swatch) : Prop:= ∀ (T':∀ i x,(A i).WPermit x a), ∀ p:I→Vantage,LightsCross a L p → StarCluster L p → P.Passport a L A T' p
variable (p:I→Vantage)(f g:I→ℝ)
local notation "Zt" p:max z:max b:max=> Function.update p z (slide a (p z) b)
lemma slide_cluster (i:I)(b:LightsCross a L p)(c:Dressing a L p f g)(k:StarCluster L p) : ∃ r> (0:ℝ),∀ d:ℝ,|d|<r→ let p':=Zt p i d; LightsCross a L p' ∧ Dressing a L p' f g ∧ StarCluster L p':=by
 classical
 -- buy cluster too via openness on any other aspect. Use open sets not perm order formulas for slide map directly
 let ζ(s:ℝ):= Function.update p i (slide a (p i) s)
 have he:Continuous ζ:= by
    apply continuous_pi; intro j; by_cases u:j=i
    · subst j; unfold ζ; simp_rw [Function.update_self]; exact slide_from a (p i)
    unfold ζ; simp_rw [Function.update_of_ne u]; exact continuous_const
 have ht:Tendsto ζ (𝓝 0) (𝓝 p):= he.tendsto' 0 p (by unfold ζ; rw [slide_zero,Function.update_eq_self i p]) -- check eq args
 have hL(b:Axis)(v:List I): LightsCross b v p → ∀ᶠ d in 𝓝 0,LightsCross b v (ζ d):= fun e=> ht.eventually ((space_clear b v).mem_nhds e)
 have hy:∀ᶠ d in 𝓝 0, StarCluster L (ζ d):= by
    apply eventually_all.mpr; intro j; obtain ⟨v,g₁,u⟩:= k j; exact (hL j v u).mono fun i h=> ⟨v,g₁,h⟩
 obtain ⟨r,e,v⟩:= Metric.mem_nhds_iff.mp ((hL a L b).and ((ht.eventually (dressed_stay a L p f g c)).and hy)); exact ⟨r,e,fun d p=> v (mem_ball_zero_iff.mpr p)⟩ -- mem_ball_zero_iff (maybe call rw norm_real?). `dressed_stay` not apply P per source.
-- multilinearity at that slot. avoid heavier ops.
private lemma stunt_mass {B:Hilbert}(X Y:B.Op)(D:P.Stunt→ B.Op)(p: List P.Stunt): X*(p.map (fun i=> i.wage • D i)).sum*Y=(p.map (fun i=> i.wage • (X* D i *Y))).sum := by
 induction p with
 | nil=> simp only [List.map_nil,List.sum_nil,mul_zero,zero_mul]
 | cons i l h=> rw [List.map_cons,List.sum_cons,List.map_cons,List.sum_cons,mul_add,_root_.add_mul,h,Algebra.mul_smul_comm,Algebra.smul_mul_assoc]
variable (i:I)(e:i∈L)
local notation "Rp" d:max p:max=> Function.update p i (slide a (p i) d)
local notation "A'" F:max=> Function.update A i F
local notation "Ωp" x:max B:max=> inner ℂ (P.heaven a (P.advocate 3 x a)) ((B:(P.ManyF a (Θ x a)).Op) (P.heaven a (Θ x a))) -- avoids parsing multi
local notation "Ψ₁" s:max x:max l:max p:max => P.RawPrice x a L (A' ((l:P.Stunt).performer)) (Rp ((l:P.Stunt).jump) p) f g s -- recommends whitespace errors
local notation "RpO" s:max x:max l:max p:max => P.RawOp x a L (A' ((l:P.Stunt).performer)) (Rp ((l:P.Stunt).jump) p) f g s
private lemma map_aside {I B:Type*}[DecidableEq I](x:I)(l:List I)(u:x∉l) (A:I→B)(B':B): l.map (Function.update A x B')=l.map A := by apply List.map_congr_left; intro i p; exact Function.update_of_ne (fun (e:i=x)=>u (e ▸ p)) ..
include e
lemma price_slots (l:List P.Stunt)(σ:I→ℕ)(h:L.Nodup):
    let Z:= P.VistaAct x a l (f i) (g i) (p i) (σ i)
    let V:= fun k=> (A k).scoop P x a (f k) (g k) (p k) (σ k)
    (L.map (Function.update V i Z)).prod=(l.map (fun u=> u.wage • RpO σ x u p)).sum := by
 let V:= fun k=> (A k).scoop P x a (f k) (g k) (p k) (σ k); let F(k:P.Stunt): (G).Op:= k.performer.scoop P x a (f i) (g i) (slide a (p i) k.jump) (σ i); let Z:= P.VistaAct x a l (f i) (g i) (p i) (σ i)
 obtain ⟨q,r,hq⟩:= List.append_of_mem e -- p sets inside true. order maybe hq `q ++ i::r = L`
 subst L; -- tune l not L
 let X:=(q.map V).prod; let Y:=(r.map V).prod
 have hT:= List.nodup_append.mp h
 obtain ⟨hl,h'⟩ := List.nodup_cons.mp hT.2.1
 have hk:i∉ q:= fun p=> hT.2.2 i p i (List.Mem.head ..) rfl -- might bind List.disjoint? check
 have he(k:P.Stunt): P.RawOp x a (q++i::r) (A' k.performer) (Rp k.jump p) f g σ=X*F k*Y:=by
    have hx: (fun i'=> ((A' k.performer) i').scoop P x a (f i') (g i') ((Rp k.jump p) i') (σ i'))= Function.update V i (F k):=by
       funext z; by_cases Hz:z=i
       · subst z; simp only [Function.update_self]; rfl
       rw [Function.update_of_ne Hz,Function.update_of_ne Hz,Function.update_of_ne Hz]
    unfold RawOp; rw [hx,List.map_append,List.prod_append,List.map_cons,List.prod_cons,map_aside i q hk,map_aside i r hl,Function.update_self,mul_assoc X]; -- after rw default no goals test
 change ((q++i::r).map (Function.update V i Z)).prod= _; simp_rw [he]; rw [List.map_append,List.prod_append,List.map_cons,List.prod_cons,map_aside i q hk,map_aside i r hl,Function.update_self]; change X*( (l.map (fun k=> k.wage • F k)).sum * Y)= _; rw [←mul_assoc]; exact stunt_mass P X Y F l

lemma price_prevision (l:List P.Stunt)(σ:I→ℕ)(h:L.Nodup):
    let Z:= P.VistaAct x a l (f i) (g i) (p i) (σ i)
    let V:= fun k=> (A k).scoop P x a (f k) (g k) (p k) (σ k)
    Ωp x ((L.map (Function.update V i Z)).prod)=(l.map (fun u=> u.wage • Ψ₁ σ x u p)).sum := by
 let Z:=(l.map (fun u=>u.wage • RpO σ x u p)).sum; let Q:=(innerSL ℂ Ω).comp (ContinuousLinearMap.apply ℂ (P.ManyF a ξ).space Ω)
 dsimp only; rw [P.price_slots x a L A p f g i e l σ h]; change Q ((l.map (fun u=> u.wage • RpO σ x u p)).sum)=_; rw [map_list_sum,List.map_map]; apply congrArg List.sum; exact List.map_congr_left fun i t=>map_smul Q i.wage _

-- scalar continuation if each causal estimate, use lifts per stunt. Induct with `Agrees.plus`, constant multipliers with scaling on dist. This doesn't yet assert field derivatives at chart ties.
omit e in
private lemma paid_later (l:List P.Stunt)(Q:P.Stunt→ℕ→P.Spectrum0 3→ℂ)(h:∀ i∈l,∃ B:P.Spectrum0 3→ℂ,Agrees atTop (Q i) (fun _=>B)):
    ∃ M:P.Spectrum0 3→ℂ, Agrees (b:=fun _=>ℂ) atTop (fun j x=> (l.map fun k=> k.wage • Q k j x).sum) (fun _ x=> M x) := by
 induction l with
 | nil=> exact ⟨fun _=>0,Agrees.refl (fun _ _=>0)⟩
 | cons k l ih=>
    obtain ⟨F,v⟩:= h k (List.Mem.head ..); obtain ⟨G',u⟩:= ih fun j v=>h j (List.Mem.tail _ v); let D:= k.wage
    have p: Agrees (b:=fun _=>ℂ) atTop (fun j x=>D • Q k j x) (fun _ x=> D • F x):=by
       intro r t; let ε:=r/(‖D‖+1); have ht:0<ε:= by unfold ε; positivity
       filter_upwards [v ε ht] with i h x; rw [dist_eq_norm,← smul_sub,norm_smul,← dist_eq_norm]; exact (mul_le_mul_of_nonneg_left (h x) (norm_nonneg _)).trans (by have hp:ε*(‖D‖+1)=r:= div_mul_cancel₀ r (by positivity); linarith)
    exact ⟨fun i=> D • F i+G' i,p.plus u⟩

-- Replace a single slot and charge other stamps with only their own papers. All height/reindex arbitrary, not rotating the domain.
lemma via_stunts (K:Set P.Swatch)(U:P.Sponsor a K (A i))(k:∀ B∈K,P.Commission a B)(xH:P.all_desk a A) (t:∀ B∈K,P.Paper a L (Function.update A i B)) : P.Paper a L A:=by
 -- buy at any constellation with actual gap. Always have shapes; no assumption I Finite. Arch words use each stamp symbol only once (order from pose).
 classical
 intro X₀ p L₀ p' σ q z u; obtain ⟨f,g,w⟩:=sews a L p L₀; let Ξ(i:ℕ)(x:P.Spectrum0 3):= P.RawPrice x a L A (q i) f g (σ i); let Y(x:P.Spectrum0 3):=P.ChartPrice x a L (fun i=>(X₀ i x).atHeat) p f g
 let MX(p₀:ℝ):=Y
 have he:∀ (x:P.Spectrum0 3),P.EuCost x a L (fun i=>(X₀ i x).atHeat) p=Y x:=fun x=> P.Eu_pays x a L p A _ f g L₀ w -- got variable local notation Θ name conflict! rename
 have hb(j:I):=(xH j).threshold; have hx(j:I)(v₁:j∈L):=(xH j).being
 unfold CoPays; simp_rw [he]; apply (P.wearing a L p A f g w z hx u).trans
 change Agrees (b:=fun _=>ℂ) atTop (fun i x=>P.RawPrice x a L A (q i) f g (σ i)) (fun _ x=> Y x)
 apply learns_price; · intro x; exact (show Tendsto _ _ _ from tendsto_const_nhds.inner ((P.chart_flies x a L p A (fun i=> X₀ i x) f g w z u) (P.heaven a (P.advocate 3 x a))).1) -- may need explicit
 intro ε k₁
 let d:=ε/2; have hd:0<d:=half_pos k₁
 obtain ⟨C,pC,h⟩:= P.reach_cost a L p A f g w hx (fun i _=>hb i); obtain ⟨Xt,hZ,F⟩:= limit_ticket (s:=atTop) (J:=ℕ) L (fun x=>P.stoves_paidOne x a) C pC d hd -- notation Xt variable adjust
 obtain ⟨r,h0,t0⟩:= slide_cluster a L p f g i L₀ w p'; obtain ⟨s,U',v,hh⟩:= clock_enough (f i) (g i) (p i a) (w.1 i e).1 (w.1 i e).2
 obtain ⟨l,L₁,h'⟩:= U s U' r Xt h0 hZ
 let q'(u:P.Stunt)(k:ℕ):= Function.update (q k) i (slide a (q k i) u.jump); let B(k:P.Stunt):= Function.update A i k.performer; let ψ(k:P.Stunt)(n:ℕ)(x:P.Spectrum0 3):= P.RawPrice x a L (B k) (q' k n) f g (σ n)
 have hm(b:P.Stunt)(y:b∈l): ∃ M:P.Spectrum0 3→ℂ, Agrees atTop (ψ b) (fun _=>M):=by
    let pM:= Function.update p i (slide a (p i) b.jump); obtain ⟨v₀,u₀,V⟩:= t0 b.jump (L₁ b y).2.1; let hb:= (L₁ b y).1; let H':= P.all_desk_update a A xH i b.performer (k b.performer hb)
    let X(j:I):=(H' j).all; have pX(j:I)(U:j∈L): Tendsto (fun k=> q' b k j) atTop (𝓝 (pM j)):=by
       unfold q' pM; by_cases h:j=i
       · subst j; simp_rw [Function.update_self]; exact ((slide_to a b.jump).tendsto _).comp (u i U)
       simp_rw [Function.update_of_ne h]; exact u j U
    exact ⟨fun x=> P.EuCost x a L (fun i=>(X i x).atHeat) pM, ((P.wearing a L pM (B b) f g u₀ z (fun j _=>(H' j).being) pX).symm).trans ((t b.performer hb) X pM v₀ V σ _ z pX)⟩
 obtain ⟨M,hm'⟩:= paid_later P l ψ hm
 let Xb(j:I)(k:ℕ)(x:P.Spectrum0 3):=(A j).scoop P x a (f j) (g j) (q k j) (σ k j)
 let X(k:ℕ)(x:P.Spectrum0 3):= P.VistaAct x a l (f i) (g i) (q k i) (σ k i); let X' (j:I)(k:ℕ)(x:P.Spectrum0 3):= Function.update (fun j=>Xb j k x) i (X k x) j
 have hp: UpTo (b:=fun x=>GOp x) atTop (fun k x=>P.RawOp x a L A (q k) f g (σ k)) (fun k x=>(L.map (fun j=>X' j k x)).prod) d :=by
    refine F Xb X' (fun i e=>h i e _ _ (u i e) (z i e)) (fun j p=>?_) -- p shadows p
    unfold X'; by_cases Hc:j=i
    · subst j; simp_rw [Function.update_self]; exact P.anchor_over a (A i) (f i) (g i) _ s v hh U' l _ (u i p) _ (z i p) Xt h' ((xH i).being) (fun i e=>⟨(L₁ i e).2.2,(k i.performer (L₁ i e).1).being⟩) -- .2.2 only. fix
    simp_rw [Function.update_of_ne Hc]; exact Agrees.refl (Xb j) Xt hZ
 have hu:L.Nodup:= L₀.imp (fun c p=>by rcases p with rfl; exact lt_irrefl _ c)
 have hv := hp.verify (fun x=> P.heaven a (P.advocate 3 x a)) (fun x=> P.stone_norm a (P.advocate 3 x a)); refine ⟨M, add_halves ε ▸ (?_ : UpTo _ _ _ (d+d))⟩; refine hv.chain (?_ : UpTo _ _ _ d)
 have hx: (fun (n:ℕ)(x:P.Spectrum0 3)=>Ωp x ((L.map (fun j=>X' j n x)).prod)) = fun (n:ℕ)(x:P.Spectrum0 3)=> (l.map fun k=> k.wage • ψ k n x).sum:= funext fun k=> funext fun x=> P.price_prevision x a L A (q k) f g i e l (σ k) hu
 exact hx.symm ▸ hm' d hd -- tune HM EuCost wrapper.

end single
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.paid_later
#print axioms Spine.Paper
#print axioms Spine.price_prevision
#print axioms Spine.via_stunts
