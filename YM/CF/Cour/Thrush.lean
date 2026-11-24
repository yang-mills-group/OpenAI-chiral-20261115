import YM.CF.Cour.Tul
import YM.CF.Cour.EdgeC
import YM.CF.Levier.Hymn
import YM.CF.Hom.Sally
import YM.CF.Cour.Monet
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Cour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Tenant Proa Broc Jet MeasureTheory
open Pec Reef Levier
open scoped Matrix.Norms.L2Operator Topology BigOperators NNReal Classical ContDiff InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {ι:Type}{N m X B L:Side}{n k j:ℕ}{e d t x u C A:ℝ}
variable{G:Ratio (CSide m B) (CSide X B)}{p: Aim N}
variable {p': Aim (CSide X B)}{o: Odd L.val}{Y:Pricing j L o (Thread j)}{P:Grasp Y B e}{M:Male}
lemma ship_t (I:Pride (CSide X B))(K:Pride (CSide m B))(M:Male)(g:Pearl P)(h:Stamped j L o Y)(w:G.count=L)(b:Bool)(t:Shape)(V:nomA m X B)(p:V ∈ Rent0 G e)(u:1≤j)(hp:Ample p'.den)(hk:Cry p')(hx:P.roundZ ≤ (CSide m B).val)(hY:0< e)(J: Hops G j o p' M V)(hl:WordK I)(hd:WordK K)(hv:ClearP I)(he:ClearP K):
 shipA G P M p'.den I K (stanza G t (xtra b) V)= cSignX (b.xor (detX t.s)) (shipA G P M p'.den I K V):=by
 unfold shipA; rw [show pigment I (stanza G t (xtra b) V).1= _ from portPartH _ hl hv (t.broad G) b V.1, show pigment K (stanza G t (xtra b) V).2= _ from portPartH _ hd he t b V.2, show lush _ _ _ _ _= _ from (coast M g h w b t V p hp.self.1 u hp hk hx hY J).1]; exact (pledge ..).symm
section
variable (G e) (j k:Sweep (CSide m B)) (t:Shape)(b:Bool)
def male(x:Rent0 G e):↑(Rent0 G e):=⟨stanza G (castX j) (xtra j.charge) x.val,alongS _ _ _ _ _ x.property⟩
def jag(J:Sweep (CSide m B)):Sweep (CSide X B):= ⟨J.s,G.embed J.b,J.charge⟩
lemma jagR : jag G (j*k) = jag G j * jag G k:=by
 unfold jag; change Sweep.mk _ (G.embed (j.b+j.s.act k.b)) _=Sweep.mk _ _ _; rw [show G.embed (j.b+j.s.act k.b)=G.embed j.b+ G.embed (j.s.act k.b) from map_add G.root .. ,G.signed]; rfl
lemma impL : wrap (CSide X B) ((castX (jag G j)).t)=wrap _ ((castX j).broad G).t:=by unfold jag castX Shape.broad; dsimp only; rw [wrap_lift,←G.embed_wrap, wrap_lift]
lemma flair(j k:Shape)(p:j.s=k.s)(h:wrap N j.t=wrap N k.t)(V:Bkg (More N)): stir (xtra b) j V=stir (xtra b) k V:=by rw [←stir_e j b, p,h,stir_e] -- occurrence
lemma jag_B (x:Rent0 G e): flashA (jag G j) x.val.1=(male e G j x).val.1:=flair j.charge (castX (jag G j)) (Shape.broad G (castX j)) rfl (impL G j) x.val.1 -- wildcard
lemma male_m(x: Rent0 G e): male e G k (male e G j x)=male e G (j*k) x:=by
 apply Subtype.ext; refine Prod.ext ?_ (lights ..); rw [←jag_B,←jag_B,← jag_B]; rw [lights,← jagR]
lemma sail_ν(t:Shape): Continuous (stir (N:=N) (xtra b) t):=by
 refine continuous_pi fun i=>?_; let T:= Site (More N); let f:=fun x:Bkg (More N)=>Lattice.pull t.s (wrap _ (2 • t.t)) x i; change Continuous (polarX b ∘ f); unfold f; refine (polar_c b).comp ?_; unfold Lattice.pull; unfold Step.read; split <;> fun_prop
lemma male_c : Continuous (male e G j):= by apply Continuous.subtype_mk; exact ((sail_ν ..).comp (continuous_fst.comp continuous_subtype_val)).prodMk ((sail_ν ..).comp (continuous_snd.comp continuous_subtype_val)) -- tune inference
lemma stir_B(x y:Bkg (More N))(t:Shape)(S:Seal (Site (More N)))(p:Agrees (roarD N t S) x y): Agrees S (stir (xtra b) t x) (stir (xtra b) t y):=by
 rintro ⟨i,j⟩ h q; change (posDir j).read (stir (xtra b) t x) i= (posDir j).read (stir (xtra b) t y) i; rw [veil_x,veil_x]; apply congrArg; refine riot _ _ _ _ _ p (mem_image_of_mem _ h) ?_; rw [← salt]; exact mem_image_of_mem _ q
lemma male_r(X:Seal (Site (More (CSide X B)))) (x y:Rent0 G e)(p:(dressL G e).rel (toRoar G j X) x y): (dressL G e).rel X (male e G j x) (male e G j y):=by
 refine ⟨stir_B _ _ _ _ _ p.1,stir_B _ _ _ _ _ ?_⟩; rw [cloud_p]; exact p.2
lemma male_g(x:Rent0 G e)(g): let M:=dressL G e; male e G j (M.dress g x)= M.dress (Levier.starG j.charge (Shape.broad G (castX j)) g) (male e G j x):=by
 intro M; let A:=castX j; let B:=Shape.broad G A; let g':=Levier.starG j.charge B g
 have ht:scaleG G g'=Levier.starG j.charge A (scaleG G g):=by ext1 i; simp only [scaleG,g',Levier.starG,Function.comp_apply,B,Shape.foldsT]
 have hQ {N:Side}(a:Shape)(v:Bkg (More N))(h:Site (More N)→E): stir (xtra j.charge) a (gauge h v)=gauge (Levier.starG j.charge a h) (stir (xtra j.charge) a v):= (siren j.charge a N v (fun _=>apex) h).1
 apply Subtype.ext; refine Prod.ext (hQ B _ _) ?_; change stir _ A _=gauge (scaleG G g') _; rw [ht]; exact hQ _ x.val.2 (scaleG G g)
end
end YM.CF.Cour
