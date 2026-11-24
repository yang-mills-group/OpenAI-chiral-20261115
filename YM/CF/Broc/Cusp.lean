import YM.CF.Broc.Finch
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Broc
open Function Filter Lattice Metric Lat Finset Tenant Branch Fock Dial MeasureTheory Paige Phase Phase.Sample Brace Cube Peaks Tulip Rush
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {m B:Side}{j l b n:ℕ}{e p d a w:ℝ} (H:CoinG j l b n d a w)(G:Guide B e p d)
abbrev memo (x:backS m B e p):=x.val.1
abbrev stampA(x: backS m B e p): Skin m B:= (memo x).val.1
def tided (h:Bool)(x:backS m B e p):Sheen m B:=if h then (memo x).val.2.2 else (memo x).val.2.1
abbrev brim(x:backS m B e p): Cue m:= x.val.2
abbrev solesK (h)(x: backS m B e p):= tailP m B (tided h x) (brim x)
lemma roseV (h: Bool)(x:backS m B e p):Foil m B e p {1} (solesK h x) (tided h x) (stampA x):=by
 apply att_dome _ (memo x).property.1; cases h; exact (memo x).property.2.1; exact (memo x).property.2.2
 cases h; exact (sealS ..).1; exact (sealS ..).2 -- tune
lemma stateC(h:Bool):Continuous (fun x:backS m B e p=> ((stampA x,solesK h x,tided h x,stick 1):hip m B)):=by
 have hv:Continuous (fun x:backS m B e p=> (memo x).val):=continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)
 have hc:Continuous (fun x:backS m B e p=>tided h x):=by cases h; exact continuous_fst.comp (continuous_snd.comp hv); exact continuous_snd.comp (continuous_snd.comp hv)
 have ht:Continuous (fun x:backS m B e p=>solesK h x):=by
   let hx: Continuous (fun x:backS m B e p=>brim x):=continuous_snd.comp continuous_subtype_val; apply continuous_pi; intro i; simp only [solesK,tailP,capRow,arrayZ]; split <;> first | exact (continuous_apply _).comp hx | exact (continuous_apply _).comp hc
 exact (continuous_fst.comp hv).prodMk (ht.prodMk (hc.prodMk continuous_const))
include H G
def ticketX {m B:Side}{e p:ℝ}(b:Bool)(i:ℕ)(n:ℕ)(x:backS m B e p):=ark m B (stampA x) (solesK b x) (tided b x) (berth n i) (stick 1)
lemma rolling (x:backS m B e p)(h:Bool){i:ℕ}(p:i<n): Gaze (stampA x) (ticketX h i n x) (ticketX h (i+1) n x) d:=rail_g H G (roseV h x) (stick_in _ (mem_singleton_self _)) _ p
abbrev rollP (h:Bool)(i n:ℕ)(x:backS m B e p): Sew (CSide m B) (CSide m B) := couple (stampA x) (ticketX h i n x) (ticketX h (i+1) n x)
def beckL(h:Bool)(i:ℕ)(q:i<n)(H:CoinG j l b n d a w)(G:Guide B e p d)(x:backS m B e p): Loom (idrat (CSide m B)) d:= ⟨rollP h i n x,Gaze.glimp _ _ _ (rolling H G x h q) H.posT⟩
lemma tixC(h:Bool){i:ℕ}(v:i≤ n): Continuous (fun x:backS m B e p=> ticketX h i n x):=by
 have ht: berth n i∈ Set.Icc 0 1:= by rw [←term_eq n H.steps i v]; exact (termJ n i).property
 refine continuous_iff_continuousAt.mpr fun x=>?_ ; let F:=fun x:backS m B e p=>(stampA x,solesK h x,tided h x,stick 1)
 let P:hip m B→ Sheen m B:=fun q=> ark m B q.1 q.2.1 q.2.2.1 (berth n i) q.2.2.2
 have he: ContinuousAt P (F x):= ark_at e p _ _ _ G (F x) (roseV h x) (stick_in 1 (mem_singleton_self _)) ht
 exact he.comp (f:=F) ((show Continuous F from stateC h).continuousAt)
lemma beck_c(h:Bool){i:ℕ}(v:i<n):Continuous (beckL (m:=m) h i v H G) :=by
 refine Continuous.subtype_mk ?_ _; have hz:Continuous (fun x:backS m B e p=> (memo x).val):=continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val); have ht:= continuous_fst.comp hz;
 exact (ht.prodMk ht).prodMk ((tixC (m:=m) H G h (show i+1≤n from v)).prodMk (tixC H G h v.le))
omit H G
lemma local_arc(h:Bool)(i n:ℕ)(S:Table m B)(x y:backS m B e p)(g: (forestB m B e p).botL.rel (foam _ (8*B.val) S) x y) : AgreeF S (ticketX h i n x) (ticketX h i n y):=by
 let t:=foam _ (8*B.val) S; have hp: AgreeF t (tided h x) (tided h y):=by cases h; exact g.1.2.1; exact g.1.2.2
 have he(q:Spot m)(h':q.1∈complexA m B t):solesK h x q=solesK h y q:=by
   unfold solesK tailP capRow arrayZ; split; exact g.2 _ h'; exact hp _ ((mem_filter.mp h').2 (raddr ..))
 intro z hz
 have hx:= commonA (stick 1) (S:=S) (U:=stampA x) (V:=stampA y) g.1.1 he z hz
 unfold ticketX ark roofV; rw [hx,show hook (tided h x) z=hook (tided h y) z from congrArg Subtype.val (hp z (foam_in _ _ S hz))]
include H G
variable (hm:b≤ (CSide m B).val)
include hm
lemma fare_c (h:Bool)(x:backS m B e p)(g:Fend (CSide m B)→SU.E)(i:ℕ)(v:i≤n): ticketX h i n ((forestB m B e p).pool g x)=feast g (ticketX h i n x):= by
 let y:= (forestB m B e p).pool g x; have hu:tided h y=feast g (tided h x):=by cases h <;> rfl
 have he:solesK h y=onF g (solesK h x):=by unfold solesK tailP; rw [hu]; funext i; by_cases v:i.2=1 <;> simp only [onF,capRow,v,ite_true,ite_false,arrayZ] <;> rfl
 change ark _ _ (gauge g _) (solesK _ y) _ _ _= _; rw [he,hu]; -- Hop_r needs hm included! hm not needed remove h
 exact hop_r H G hm g (roseV h x) (stick_in _ (Finset.mem_singleton_self 1)) ((term_eq n H.steps i v) ▸ (termJ n i).property)
end YM.CF.Broc
