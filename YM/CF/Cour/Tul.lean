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
abbrev Hops (G:Ratio (CSide m B) (CSide X B))(j:ℕ)(o:Odd L.val)(W:Aim (CSide X B))(M: Male)(x:nomA m X B):Prop:= ‖coatG L o j G M W.den x‖<1 ∧‖leftN L j o G M x (W.den x.1)‖<1 ∧ IsUnit (Peaks.cloth j M G (unionP x))
lemma coast(M:Male)(g:Pearl P)(h:Stamped j L o Y)(w:G.count=L)(b:Bool)(t:Shape)(V:nomA m X B)(p:V ∈ Rent0 G e)(k:p'.den 1=0)(u:1≤j)(hp:Ample p'.den)(hk:Cry p')(hx:P.roundZ ≤ (CSide m B).val)(hY:0< e)(J: Hops G j o p' M V):
 let Q:=stanza G t (xtra b) V; let f(T:nomA m X B):=era L j o G M T (p'.den T.1); lush G P M p'.den Q=cSignX (b.xor (detX t.s)) (lush G P M p'.den V) ∧ f Q=yank b t (spinU b t.s) (f V):=by
 intro W f; let C (T:nomA m X B):=p'.den T.1; let Z(T):= crux j G M T (C T); let A (y:nomA m X B):= foal j true M G (unionP y)
 have hl(y:nomA m X B)(hy:y∈Rent0 G e):∀ i, Along j L o (Thread j) i M G (unionP y):=by
    obtain ⟨v,hv⟩:= Phase.cue_from y.2; let U:=Brace.starfish m B y.2 v; have ht:=pose_g P hY G w hx y hy U (Brace.starK P.capY hY.le (JointB.cg hy) hv); exact (Y.cap G w (P.needed.trans hx) M _ ht.glyph).chart -- tune names
 have hz: W∈Rent0 G e:= alongS _ _ _ _ _ p; let X':=spinU b t.s; let S:=pflux t G X' (xtra b); let r:=detX t.s
 obtain ⟨hu,hV,hD⟩:=J; obtain ⟨hm,hW,hT⟩:=unitedX h hY u G w hx M _ p (Z V) (tag_g _ (hl V p true).lead) hD t (xtra b) X' (spinZ ..) hu hV
 have hg:Odd G.count.val:=w.symm ▸ o
 have hv:Z W= Thera.jazz r (sings b S (Z V)):=by
    let D:= (spinZ b t.s); have he : sings b S (A V)=swapX r (A W):=by
       have hx : sings b S (A V)=foal j (r.xor true) M G (unionP W):=(hoarD G hg t _ _ D j u M Y.e V (ampleB p P.gem) (h.fields_one _ (P.needed.trans hx)) (h.fields_one _ (P.needed.trans (P.clock_fine G hx))) true).1
       rw [hx]; cases r; rfl; exact foil_neg _ _ true .. -- tune
    have hJ (v:Op (Single (CSide X B))):foot G (Thera.jazz r v)=Thera.jazz r (foot G v):=by cases r<;> rfl
    have hC: C W= yank b (t.broad G) X' (C V):=peak_f p' hp hk (Shape.broad G t) b X' D V.1
    unfold Z crux; rw [hC]; change capT _ (foot G (Thera.jazz r (sings b _ _)))=_; rw [hJ,←portFoot G hg]; exact prima S (A V) _ _ ((hl W hz true).lead) he
 constructor
 · unfold lush; change -(altar _ _ W M)- invoice (desire L j o G M W (Z W))= _; rw [hv,hW,show altar G P W M=_ from chain_sym g h hx u G w hY V p M t b]; change _=cSignX _ (-_ - invoice (desire L j o G M V (Z V))); generalize altar G P V M=T; cases h:b.xor (detX t.s)<;>simp [cSignX]
 change fruit _ _ _ _ _ _ (Z W)= _; rw [hv]; exact hT
end YM.CF.Cour
