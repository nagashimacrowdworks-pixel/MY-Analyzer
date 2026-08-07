import os, sys, calendar, webbrowser, tempfile, re, threading, time
import tkinter as tk
from tkinter import ttk, filedialog, messagebox, simpledialog
import tkinter.font as tkfont
import pandas as pd
import matplotlib.pyplot as plt
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
from datetime import datetime
import requests
from bs4 import BeautifulSoup
import subprocess
import urllib.request

try:
    from selenium import webdriver
    from selenium.webdriver.edge.service import Service as EdgeService
    from selenium.webdriver.edge.options import Options as EdgeOptions
    from selenium.webdriver.common.by import By
    
    # 【追加: exe化時のエラー対策】
    # PyInstallerでexe化した際に隠しモジュールが欠落して「No module named 'selenium.webdriver...'」
    # エラーになるのを防ぐため、内部モジュールを明示的にインポートしておきます。
    import selenium.webdriver.common.bidi.cdp
    import selenium.webdriver.common.devtools
    import selenium.webdriver.edge.webdriver
    import selenium.webdriver.remote.webdriver
except ImportError:
    webdriver = None

# 【追加】画像貼り付け機能用
try:
    from PIL import Image, ImageGrab, ImageTk
    import io
    import base64
    PILLOW_AVAILABLE = True
except ImportError:
    PILLOW_AVAILABLE = False

# --- 基本設定 ---
APP_VERSION = "1.3"  # 現在のアプリのバージョン
CBG, CCARD, CTXT = "#f0f4f8", "#ffffff", "#000000"
CPRI, CACC = "#0056b3", "#fd7e14"
CHL, CSAT, CSUN = "#e3f2fd", "#2b6cb0", "#c53030"
W_JA = ["日", "月", "火", "水", "木", "金", "土"]
plt.rcParams['font.family'] = 'MS Gothic'

RENAME_DIC = {"Name": "ドライバー名", "ｱｽｸﾙ": "アスクル", "ｼﾞｮｲﾝ": "ジョイン", "N'sｺﾋﾟｰ": "エヌズコピー", "N‘sコピー": "エヌズコピー", "N's薬品": "エヌズ医薬", "N‘s薬品": "エヌズ医薬", "SBS": "SBS配送", "アスクル返品": "その他回収", "電報": "ヒューモニー", "代引": "SBS代引", "段ﾎﾞｰﾙ回収": "段ボール回収", "ﾄﾅｰ回収": "トナー回収", "ﾁｬｰﾀｰ①": "チャーター①", "ﾁｬｰﾀ②": "チャーター②", "ﾁｬｰﾀ③": "チャーター③", "ﾁｬｰﾀｰ①詳細": "チャーター①詳細", "ﾁｬｰﾀ②詳細": "チャーター②詳細", "ﾁｬｰﾀ③詳細": "チャーター③詳細", "他": "西湘その他", "備考1": "備考１", "備考2": "備考２", "備考3": "備考３"}
MULTI_COLORS = ["#1f77b4", "#ff7f0e", "#2ca02c", "#d62728", "#9467bd", "#8c564b", "#e377c2", "#7f7f7f", "#bcbd22", "#17becf", "#aec7e8", "#ffbb78", "#98df8a", "#ff9896", "#c5b0d5", "#c49c94", "#f7b6d2", "#c7c7c7", "#dbdb8d", "#9edae5"]

class AppToolTip:
    def __init__(self):
        self.tw = None

    def show(self, x, y, text):
        if self.tw: self.hide()
        self.tw = tk.Toplevel()
        self.tw.wm_overrideredirect(True)
        self.tw.attributes("-topmost", True)
        
        lbl = tk.Label(self.tw, text=text, justify=tk.LEFT, background="#ffffe0", relief=tk.SOLID, borderwidth=1, font=("MS Gothic", 12, "bold"))
        lbl.pack(ipadx=5, ipady=5)
        
        self.tw.update_idletasks()
        w = self.tw.winfo_width()
        h = self.tw.winfo_height()
        
        sw = self.tw.winfo_screenwidth()
        sh = self.tw.winfo_screenheight()
        
        if x + w > sw: x = sw - w - 10
        if y + h > sh: y = y - h - 20 
        else: y = y + 20
        
        self.tw.wm_geometry(f"+{int(x)}+{int(y)}")

    def hide(self):
        if self.tw:
            self.tw.destroy()
            self.tw = None

class DataAnalyzerApp:
    def __init__(self, root):
        self.root = root
        self.root.title("📊 配送データ分析プラットフォーム (Ver 84.0 表データコピー対応版)")
        self.root.geometry("1620x950")
        self.root.configure(bg=CBG)
        
        if getattr(sys, 'frozen', False):
            app_path = os.path.dirname(sys.executable)
        else:
            app_path = os.path.dirname(os.path.abspath(__file__))
        self.db_path = os.path.join(app_path, "saved_dataset.pkl")

        self.all_data, self.bad_delivery_data, self.depot_map = {}, {}, {}
        self.cached_df = None
        self.bad_cached_df = None
        self.elearning_cached_df = pd.DataFrame()
        self.graph_images = {}  # ★追加：グラフ用画像を保存する辞書
        self.img_list_geo = "900x600"  # ★追加：画像一覧ウィンドウのサイズ・位置保存用
        self.my_password = None
        self.restored_ui_state = None
        self.auto_lock_time_str = "5分"
        self.auto_lock_timer_id = None
        
        self.links = [
            {"name": "リンク1未設定", "url": ""},
            {"name": "リンク2未設定", "url": ""},
            {"name": "リンク3未設定", "url": ""}
        ]
        
        self.multi_items_a = []
        self.multi_items_b = []
        self.multi_drv_list = []
        
        self._upd_job = None
        self._bad_job = None
        self._menu_check_job = None

        self.root.protocol("WM_DELETE_WINDOW", self.on_closing)

        sw = self.root.winfo_screenwidth()
        if sw >= 2560: self.f_size = 15
        elif sw >= 1920: self.f_size = 14
        elif sw >= 1600: self.f_size = 13
        elif sw >= 1366: self.f_size = 12
        else: self.f_size = 11

        self.t2_u = "month"
        self.show_b2 = False

        self.tooltip = AppToolTip()
        self.hover_cids = {}

        self.fn = tkfont.Font(family="MS Gothic", size=self.f_size, weight="bold")
        self.fb = tkfont.Font(family="MS Gothic", size=self.f_size, weight="bold")
        self.ft = tkfont.Font(family="MS Gothic", size=self.f_size + 2, weight="bold")
        self.fs = tkfont.Font(family="MS Gothic", size=self.f_size - 3, weight="bold")

        self.num_f = ["全体個数", "アスクル", "LOHACO", "トナー回収", "その他回収", "カタログ配送", "外販", "SBS配送", "SBS代引", "SBS集荷", "ヒューモニー", "エヌズ医薬", "エヌズコピー", "西湘その他", "ジョイン", "エコ配", "カウネット", "LO夜", "段ボール回収", "チャーター①", "チャーター②", "チャーター③"]
        self.txt_f = ["チャーター①詳細", "チャーター②詳細", "チャーター③詳細", "備考１", "備考２"]
        self.v_cols = ["ドライバー名", "所属デポ"] + self.num_f + self.txt_f
        self.b_cols = ["配送日", "デポ名", "ドライバ名", "荷主名称", "問合せ中分類"]

        self.style = ttk.Style()
        try: self.style.theme_use("default")
        except: pass
        self.style.configure(".", background=CBG, foreground=CTXT, font=self.fn)
        self.style.configure("TNotebook", background=CBG)
        rh = int(self.f_size * 2.4); rh = 16 if rh < 16 else rh
        self.style.configure("Treeview", rowheight=rh, font=self.fn)
        self.style.configure("Treeview.Heading", font=self.fb)
        
        self.create_widgets()
        self.load_db() 
        
        self.create_login_overlay()
        
        self.root.bind("<Control-p>", self.print_graph)
        
        # --- オートロック用のイベント監視 ---
        self.root.bind_all("<Motion>", self.reset_idle_timer)
        self.root.bind_all("<KeyPress>", self.reset_idle_timer)
        self.root.bind_all("<ButtonPress>", self.reset_idle_timer)
        
        try:
            self.root.state('zoomed')
        except Exception:
            self.root.attributes('-zoomed', True)
            
        # --- 自動アップデートチェックをバックグラウンドで開始 ---
        if getattr(sys, 'frozen', False):
            threading.Thread(target=self.check_for_update_bg, daemon=True).start()

    def on_closing(self):
        self.save_db()
        self.root.destroy()
        os._exit(0)

    def check_for_update_bg(self):
        try:
            # GitHubのversion.txt (Raw URL) から最新バージョン番号を取得
            url = "https://raw.githubusercontent.com/nagashimacrowdworks-pixel/MY-Analyzer/main/version.txt"
            response = requests.get(url, timeout=5)
            if response.status_code == 200:
                latest_version_str = response.text.strip()
                try:
                    current_v = float(APP_VERSION)
                    latest_v = float(latest_version_str)
                    if latest_v > current_v:
                        self.root.after(2000, lambda: self.prompt_update(latest_version_str))
                except ValueError:
                    if latest_version_str != APP_VERSION:
                        self.root.after(2000, lambda: self.prompt_update(latest_version_str))
        except Exception as e:
            print(f"Update check failed: {e}")

    def prompt_update(self, latest_version):
        if messagebox.askyesno("アップデートのお知らせ", f"新しいバージョン (V{latest_version}) が見つかりました。\n今すぐアップデートしますか？\n（数秒〜数十秒かかり、自動で再起動します）"):
            self.run_auto_update()

    def run_auto_update(self):
        upd_win = tk.Toplevel(self.root)
        upd_win.title("アップデート中...")
        upd_win.geometry("400x150")
        upd_win.configure(bg=CBG)
        upd_win.transient(self.root)
        upd_win.grab_set()
        
        tk.Label(upd_win, text="最新版をダウンロードしています...\nしばらくお待ちください。", font=self.ft, bg=CBG, fg=CPRI).pack(pady=30)
        upd_win.update()
        
        def _do_update():
            try:
                exe_path = sys.executable
                exe_dir = os.path.dirname(exe_path)
                new_exe_path = os.path.join(exe_dir, "Data_Analyzer_new.exe")
                
                # GitHubの最新リリースからData_Analyzer.exeをダウンロード
                download_url = "https://github.com/nagashimacrowdworks-pixel/MY-Analyzer/releases/latest/download/Data_Analyzer.exe"
                urllib.request.urlretrieve(download_url, new_exe_path)
                
                # バッチファイルの作成
                bat_path = os.path.join(exe_dir, "update.bat")
                current_exe_name = os.path.basename(exe_path)
                
                bat_content = f"""@echo off
:DEL_LOOP
timeout /t 1 /nobreak > nul
del "{current_exe_name}" > nul 2>&1
if exist "{current_exe_name}" goto DEL_LOOP
:REN_LOOP
ren "Data_Analyzer_new.exe" "{current_exe_name}" > nul 2>&1
if not exist "{current_exe_name}" (
    timeout /t 1 /nobreak > nul
    goto REN_LOOP
)
start "" "{current_exe_name}"
del "%~f0"
"""
                with open(bat_path, "w", encoding="shift_jis") as f:
                    f.write(bat_content)
                
                # バッチファイルを実行
                subprocess.Popen(["cmd.exe", "/c", "update.bat"], cwd=exe_dir, creationflags=subprocess.CREATE_NO_WINDOW)
                
                # アプリを安全に終了（一時フォルダのお片付けを正常に走らせる）
                def _safe_exit():
                    self.save_db()
                    self.root.quit()
                    self.root.destroy()
                    sys.exit(0)
                    
                self.root.after(100, _safe_exit)
                
            except Exception as e:
                self.root.after(0, lambda: messagebox.showerror("アップデート失敗", f"アップデート中にエラーが発生しました:\n{e}", parent=upd_win))
                self.root.after(0, upd_win.destroy)

        threading.Thread(target=_do_update, daemon=True).start()

    def IsTesting(self):
        return False
        
    def get_sort_key(self, text):
        if not isinstance(text, str):
            return b""
        k = "".join(chr(ord(c) + 0x60) if 0x3041 <= ord(c) <= 0x3096 else c for c in text)
        try:
            return k.encode('cp932')
        except:
            return k.encode('utf-8')

    def cln_dep(self, n):
        if not n or pd.isna(n): return "未登録"
        s = str(n).strip()
        for p in ["神奈川_西湘運輸_", "神奈川_西湘_", "西湘運輸_", "神奈川_"]:
            if s.startswith(p): s = s[len(p):]
        return s

    def get_driver_depot(self, name):
        if not name or pd.isna(name): return "未登録"
        n = str(name).strip()
        if n in self.depot_map:
            return self.depot_map[n]
            
        n_clean = n.replace(" ", "").replace("　", "")
        sorted_keys = sorted(self.depot_map.keys(), key=lambda x: len(str(x)), reverse=True)
        for k in sorted_keys:
            k_clean = str(k).strip().replace(" ", "").replace("　", "")
            if k_clean and k_clean in n_clean:
                return self.depot_map[k]
        return "未登録"

    def clr_p(self, ax, cv, msg="データなし", show_img_links=False):
        ax.clear()
        ax.axis('off')
        ax.text(0.5, 0.5, msg, ha='center', va='center', fontsize=self.f_size, color="#6c757d", fontname="MS Gothic", weight="bold")
        if show_img_links:
            self._draw_image_links(ax, cv)
        else:
            cv.draw()

    def _update_cache(self):
        bl = [v for v in self.all_data.values() if isinstance(v, pd.DataFrame)]
        if bl:
            df = pd.concat(bl, ignore_index=True, sort=False)
            if "日付" in df.columns:
                df["_dt"] = pd.to_datetime(df["日付"], errors='coerce')
            self.cached_df = df
        else:
            self.cached_df = None
            
        bbl = [v for v in self.bad_delivery_data.values() if isinstance(v, pd.DataFrame)]
        if bbl:
            bdf = pd.concat(bbl, ignore_index=True, sort=False)
            if "配送日" in bdf.columns:
                ext_dt = bdf["配送日"].astype(str).str.extract(r'(\d{4}[-/]\d{1,2}[-/]\d{1,2})')[0]
                bdf["_dt"] = pd.to_datetime(ext_dt, errors='coerce').fillna(pd.to_datetime(bdf["配送日"], errors='coerce'))
            self.bad_cached_df = bdf
        else:
            self.bad_cached_df = None

    def request_upd(self, e=None):
        if self._upd_job is not None:
            self.root.after_cancel(self._upd_job)
        self._upd_job = self.root.after(300, lambda: self.upd())

    def request_ref_bad(self, e=None):
        if self._bad_job is not None:
            self.root.after_cancel(self._bad_job)
        self._bad_job = self.root.after(300, self.ref_bad)

    def print_graph(self, event=None):
        try:
            idx = self.nb.index("current")
            
            # --- SBS追跡タブ (インデックス4) の場合の特別処理 ---
            if idx == 4:
                if not getattr(self, 'latest_sbs_screenshots', None):
                    messagebox.showinfo("印刷", "現在表示されているSBS追跡のデータがありません。\n検索を実行してからお試しください。")
                    return
                
                tmp_dir = tempfile.gettempdir()
                timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
                img_paths = []
                
                # 画像結合を行わず、取得したスクリーンショットをそのまま1枚ずつ保存する
                for i, data in enumerate(self.latest_sbs_screenshots):
                    img_path = os.path.join(tmp_dir, f"SBS_Track_{i+1}_{timestamp}.png")
                    with open(img_path, "wb") as f:
                        f.write(data)
                    img_paths.append(img_path)
                        
                for img_path in img_paths:
                    try:
                        os.startfile(img_path, "print")
                    except Exception:
                        os.startfile(img_path)
                        messagebox.showinfo("印刷", "自動印刷ダイアログを開けませんでした。\n画像ファイルを開きましたので、手動で印刷（Ctrl+P）してください。")
                    time.sleep(1)
                return
            # --------------------------------------------------
            
            fig_dict = {1: self.f2, 2: self.f4, 3: getattr(self, 'f_el', None)}
            
            fig = fig_dict.get(idx)
            if fig is None:
                messagebox.showinfo("印刷", "現在表示しているタブには印刷可能なグラフがありません。\n（グラフ・比較タブ、不良配送タブ、e-ラーニングタブ、SBS追跡タブを選択してください）")
                return
                
            comment = simpledialog.askstring("印刷コメント", "グラフに差し込む目立つコメントを入力してください\n（空欄・キャンセルの場合はそのまま印刷されます）:")
            orig_size = fig.get_size_inches()
            
            # --- ここから印刷用の一時レイアウト変更 ---
            fig.set_size_inches(11.69, 8.27)
            fig.tight_layout()
            
            added_texts = []
            if comment and comment.strip():
                txt = fig.text(0.5, 0.98, comment.strip(), ha='center', va='top', 
                               fontsize=24, color='red', weight='bold', 
                               bbox=dict(facecolor='yellow', alpha=0.9, edgecolor='red', boxstyle='round,pad=0.3'))
                added_texts.append(txt)
                
            tmp_dir = tempfile.gettempdir()
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            img_path = os.path.join(tmp_dir, f"Graph_{timestamp}.png")
            
            fig.savefig(img_path, dpi=200)
            
            for txt in added_texts: txt.remove()
            fig.set_size_inches(orig_size)
            fig.tight_layout()
            fig.canvas.draw()
            
            try: os.startfile(img_path, "print")
            except Exception:
                os.startfile(img_path)
                messagebox.showinfo("印刷", "自動印刷ダイアログを開けませんでした。\n画像ファイルを開きましたので、手動で印刷（Ctrl+P）してください。")
        except Exception as e:
            messagebox.showerror("印刷エラー", f"印刷処理中にエラーが発生しました:\n{e}")

    def email_graph(self, event=None):
        try:
            idx = self.nb.index("current")
            
            # --- SBS追跡タブ (インデックス4) の場合の特別処理 ---
            if idx == 4:
                if not getattr(self, 'latest_sbs_screenshots', None):
                    messagebox.showinfo("メール送信", "現在表示されているSBS追跡のデータがありません。\n検索を実行してからお試しください。")
                    return
                
                tmp_dir = tempfile.gettempdir()
                timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
                img_paths = []
                
                # 画像結合を行わず、取得したスクリーンショットをそのまま1枚ずつ保存する
                for i, data in enumerate(self.latest_sbs_screenshots):
                    img_path = os.path.join(tmp_dir, f"SBS_Track_{i+1}_{timestamp}.png")
                    with open(img_path, "wb") as f:
                        f.write(data)
                    img_paths.append(img_path)
                        
                try:
                    import subprocess
                    ps_script = "$Outlook = New-Object -ComObject Outlook.Application\n"
                    ps_script += "$Mail = $Outlook.CreateItem(0)\n"
                    ps_script += "$Mail.Subject = '【共有】SBS追跡結果'\n"
                    ps_script += "$Mail.Body = 'SBS追跡結果のスクリーンショットを共有します。`n添付の画像データをご確認ください。'\n"
                    for p in img_paths:
                        p_escaped = p.replace("'", "''")
                        ps_script += f"$Mail.Attachments.Add('{p_escaped}')\n"
                    ps_script += "$Mail.Display()\n"
                    
                    creationflags = getattr(subprocess, 'CREATE_NO_WINDOW', 0x08000000)
                    subprocess.run(["powershell", "-Command", ps_script], creationflags=creationflags)
                except Exception as e:
                    messagebox.showerror("Outlook起動エラー", f"Outlookの起動に失敗しました。\n詳細: {e}")
                return
            # --------------------------------------------------

            fig_dict = {1: self.f2, 2: self.f4, 3: getattr(self, 'f_el', None)}
            
            fig = fig_dict.get(idx)
            if fig is None:
                messagebox.showinfo("メール送信", "現在表示しているタブには送信可能なグラフがありません。\n（グラフ・比較タブ、不良配送タブ、e-ラーニングタブ、SBS追跡タブを選択してください）")
                return
                
            comment = simpledialog.askstring("メール用コメント", "グラフに差し込む目立つコメントを入力してください\n（空欄・キャンセルの場合はそのまま画像化されます）:")
            orig_size = fig.get_size_inches()
            
            # --- 一時レイアウト変更 ---
            fig.set_size_inches(11.69, 8.27)
            fig.tight_layout()
            
            added_texts = []
            if comment and comment.strip():
                txt = fig.text(0.5, 0.98, comment.strip(), ha='center', va='top', 
                               fontsize=24, color='red', weight='bold', 
                               bbox=dict(facecolor='yellow', alpha=0.9, edgecolor='red', boxstyle='round,pad=0.3'))
                added_texts.append(txt)
                
            tmp_dir = tempfile.gettempdir()
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            img_path = os.path.join(tmp_dir, f"Graph_{timestamp}.png")
            
            fig.savefig(img_path, dpi=200)
            
            for txt in added_texts: txt.remove()
            fig.set_size_inches(orig_size)
            fig.tight_layout()
            fig.canvas.draw()
            
            try:
                import subprocess
                ps_script = "$Outlook = New-Object -ComObject Outlook.Application\n"
                ps_script += "$Mail = $Outlook.CreateItem(0)\n"
                ps_script += "$Mail.Subject = '【共有】グラフデータ分析'\n"
                ps_script += "$Mail.Body = '配送業務データ分析プラットフォームからのグラフ共有です。`n添付の画像データをご確認ください。'\n"
                img_path_escaped = img_path.replace("'", "''")
                ps_script += f"$Mail.Attachments.Add('{img_path_escaped}')\n"
                ps_script += "$Mail.Display()\n"
                
                creationflags = getattr(subprocess, 'CREATE_NO_WINDOW', 0x08000000)
                subprocess.run(["powershell", "-Command", ps_script], creationflags=creationflags)
            except Exception as e:
                messagebox.showerror("Outlook起動エラー", f"Outlookの起動に失敗しました。Outlookがインストールされているか確認してください。\n詳細: {e}")
                
        except Exception as e:
            messagebox.showerror("送信エラー", f"メール送信処理中にエラーが発生しました:\n{e}")

    def reset_idle_timer(self, event=None):
        if getattr(self, 'auto_lock_timer_id', None):
            self.root.after_cancel(self.auto_lock_timer_id)
            self.auto_lock_timer_id = None

        if hasattr(self, 'login_overlay') and self.login_overlay.winfo_ismapped():
            return

        if getattr(self, 'auto_lock_time_str', "5分") == "なし":
            return
            
        time_map = {
            "1分": 1, "2分": 2, "3分": 3, "4分": 4, "5分": 5,
            "10分": 10, "15分": 15, "30分": 30
        }
        mins = time_map.get(self.auto_lock_time_str, 5)
        self.auto_lock_timer_id = self.root.after(mins * 60000, self.trigger_auto_lock)

    def trigger_auto_lock(self):
        self.lock_screen()
        
    def create_widgets(self):
        tb = tk.Frame(self.root, bg=CPRI, height=50); tb.pack(fill=tk.X, side=tk.TOP); tb.pack_propagate(False)
        self.menu_btn = tk.Button(tb, text="☰", font=("MS Gothic", 20, "bold"), bg="#004085", fg="white", relief=tk.FLAT, padx=25)
        self.menu_btn.pack(side=tk.LEFT, fill=tk.Y)
        self.menu_btn.bind("<Enter>", self.show_menu)
        tk.Label(tb, text="配送業務データ 総合一括分析プラットフォーム", font=self.ft, bg=CPRI, fg="white").pack(side=tk.LEFT, padx=20)
        
        self.btn_print = tk.Button(tb, text="🖨️ グラフ印刷", font=self.fb, bg="#28a745", fg="white", relief=tk.FLAT, command=self.print_graph)
        self.btn_print.pack(side=tk.RIGHT, padx=(5, 20), pady=8)
        
        self.btn_email = tk.Button(tb, text="✉️ メール添付", font=self.fb, bg="#17a2b8", fg="white", relief=tk.FLAT, command=self.email_graph)
        self.btn_email.pack(side=tk.RIGHT, padx=5, pady=8)

        self.ws = tk.Frame(self.root, bg=CBG); self.ws.pack(fill=tk.BOTH, expand=True)

        self.lm = tk.Frame(self.root, bg=CBG, width=320, bd=2, relief=tk.RAISED)
        self.m_open = False
        mp = tk.Frame(self.lm, bg=CBG, padx=10, pady=10); mp.pack(fill=tk.BOTH, expand=True)
        tk.Button(mp, text="📁 (β)個数実績登録(西湘)", command=self.ld_csv, bg=CPRI, fg="white", font=self.fb).pack(fill=tk.X, pady=3, ipady=4)
        tk.Button(mp, text="🚨 不良配送", command=self.ld_bad, bg="#be4bdb", fg="white", font=self.fb).pack(fill=tk.X, pady=3, ipady=4)
        tk.Button(mp, text="🏢 所属デポ", command=self.ld_dep, bg=CACC, fg="white", font=self.fb).pack(fill=tk.X, pady=3, ipady=4)
        ttk.Separator(mp, orient='horizontal').pack(fill=tk.X, pady=8)
        tk.Button(mp, text="🏢 デポマスター管理ツール", command=self.pop_dep, bg="#495057", fg="white", font=self.fb).pack(fill=tk.X, pady=3, ipady=4)
        tk.Button(mp, text="📅 データ読込状況カレンダー", command=self.pop_cal, bg="#495057", fg="white", font=self.fb).pack(fill=tk.X, pady=3, ipady=4)
        
        ttk.Separator(mp, orient='horizontal').pack(fill=tk.X, pady=8)
        
        self.link_labels = []
        for i in range(3):
            lbl = tk.Label(mp, text=f"🔗 {self.links[i]['name']}", fg="blue", bg=CBG, font=self.fb, cursor="hand2")
            lbl.pack(fill=tk.X, pady=(5, 0))
            lbl.bind("<Button-1>", lambda e, idx=i: self.open_link(idx))
            lbl.bind("<Button-3>", lambda e, idx=i: self.edit_link(idx))
            self.link_labels.append(lbl)
        tk.Label(mp, text="※左クリックで開く / 右クリックで編集", bg=CBG, font=self.fs, fg="#6c757d").pack(fill=tk.X, pady=(2, 10))

        ttk.Separator(mp, orient='horizontal').pack(fill=tk.X, pady=8)
        
        # --- 設定・ロックボタンを横並びで配置 ---
        bf_mp = tk.Frame(mp, bg=CBG); bf_mp.pack(side=tk.BOTTOM, fill=tk.X, pady=5)
        bf_mp.columnconfigure(0, weight=1)
        bf_mp.columnconfigure(1, weight=1)
        
        btn_set = tk.Button(bf_mp, text="⚙️ 設定", command=self.pop_settings, bg="#495057", fg="white", font=self.fb)
        btn_set.grid(row=0, column=0, sticky="ew", padx=(0, 2), ipady=4)
        
        btn_lock = tk.Button(bf_mp, text="🔒 ロック", command=self.lock_screen, bg="#6c757d", fg="white", font=self.fb)
        btn_lock.grid(row=0, column=1, sticky="ew", padx=(2, 0), ipady=4)

        self.rc = tk.Frame(self.ws, bg=CBG); self.rc.pack(fill=tk.BOTH, expand=True, padx=15, pady=15)
        
        self.ph_frame = tk.Frame(self.root, bg=CCARD)
        tk.Label(self.ph_frame, text="期間指定:", bg=CCARD, font=self.fb, fg=CPRI).pack(side=tk.LEFT, padx=(0, 5))
        self.pcb = ttk.Combobox(self.ph_frame, state="readonly", font=self.fn, values=["全期間", "日付指定 (1日)", "週間指定 (7日間)", "月間指定 (1ヶ月)", "年間指定 (12ヶ月)", "任意の期間指定"], width=16)
        self.pcb.pack(side=tk.LEFT, padx=2); self.pcb.current(0); self.pcb.bind("<<ComboboxSelected>>", self.on_p_change)
        
        self.lbl_start = tk.Label(self.ph_frame, text="開始:", bg=CCARD, font=self.fn)
        self.start_p_frame = tk.Frame(self.ph_frame, bg=CCARD)
        self.sy, self.sm, self.sd = [ttk.Combobox(self.start_p_frame, state="readonly", font=self.fn, width=w) for w in (6,4,4)]
        for cb in (self.sy, self.sm, self.sd): cb.pack(side=tk.LEFT, padx=1)
        
        self.lbl_end = tk.Label(self.ph_frame, text=" ～ 終了:", bg=CCARD, font=self.fn)
        self.end_p_frame = tk.Frame(self.ph_frame, bg=CCARD)
        self.ey, self.em, self.ed = [ttk.Combobox(self.end_p_frame, state="readonly", font=self.fn, width=w) for w in (6,4,4)]
        for cb in (self.ey, self.em, self.ed): cb.pack(side=tk.LEFT, padx=1)
        
        for cb in [self.sy, self.sm, self.sd, self.ey, self.em, self.ed]: 
            cb.bind("<<ComboboxSelected>>", self.request_upd)
            cb.bind("<Return>", self.request_upd)

        self.nb = ttk.Notebook(self.rc); self.nb.pack(fill=tk.BOTH, expand=True)
        self.t1 = tk.Frame(self.nb, bg=CCARD, bd=1, relief=tk.SOLID)
        self.t2 = tk.Frame(self.nb, bg=CCARD, bd=1, relief=tk.SOLID)
        self.t3 = tk.Frame(self.nb, bg=CCARD, bd=1, relief=tk.SOLID)
        self.t4 = tk.Frame(self.nb, bg=CCARD, bd=1, relief=tk.SOLID)
        self.t5 = tk.Frame(self.nb, bg=CCARD, bd=1, relief=tk.SOLID)
        
        self.nb.add(self.t1, text=" 📋 荷主別詳細 ")
        self.nb.add(self.t2, text=" 📅 グラフ・比較 ")
        self.nb.add(self.t3, text=" 🚨 不良配送一括分析 ")
        self.nb.add(self.t4, text=" 📚 e-ラーニング ")
        self.nb.add(self.t5, text=" 🚚 SBS追跡 ")
        self.nb.bind("<<NotebookTabChanged>>", self.on_tab_change)

        # Tab 1
        self.h1 = tk.Frame(self.t1, bg=CCARD); self.h1.pack(fill=tk.X, padx=15, pady=8)
        self.h1_top = tk.Frame(self.h1, bg=CCARD); self.h1_top.pack(fill=tk.X, pady=(0, 5))
        self.h1_bottom = tk.Frame(self.h1, bg=CCARD); self.h1_bottom.pack(fill=tk.X)
        
        tk.Label(self.h1_bottom, text="📋 個人実績一覧", font=self.ft, bg=CCARD, fg=CPRI).pack(side=tk.LEFT, pady=2)
        tk.Label(self.h1_bottom, text="| デポ絞り込:", bg=CCARD, font=self.fb).pack(side=tk.LEFT, padx=5)
        self.t1_cb = ttk.Combobox(self.h1_bottom, state="readonly", font=self.fn, width=12); self.t1_cb.pack(side=tk.LEFT)
        self.t1_cb.bind("<<ComboboxSelected>>", self.request_upd)
        tk.Label(self.h1_bottom, text="並び替え:", bg=CCARD, font=self.fb).pack(side=tk.LEFT, padx=(10, 5))
        
        self.t1_sort = ttk.Combobox(self.h1_bottom, state="readonly", font=self.fn, values=["実績(多い順)", "実績(少ない順)"], width=13)
        self.t1_sort.pack(side=tk.LEFT); self.t1_sort.current(0); self.t1_sort.bind("<<ComboboxSelected>>", self.request_upd)
        
        self.tv1 = ttk.Treeview(self.t1, columns=self.v_cols, show="headings")
        scr1y = ttk.Scrollbar(self.t1, orient=tk.VERTICAL, command=self.tv1.yview); scr1x = ttk.Scrollbar(self.t1, orient=tk.HORIZONTAL, command=self.tv1.xview)
        self.tv1.configure(yscrollcommand=scr1y.set, xscrollcommand=scr1x.set); scr1x.pack(side=tk.BOTTOM, fill=tk.X); scr1y.pack(side=tk.RIGHT, fill=tk.Y)
        self.tv1.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(10,0), pady=(0,10))
        for c in self.v_cols: self.tv1.heading(c, text=c)
        self.tv1.column("ドライバー名", anchor=tk.W, width=int(self.f_size * 11)); self.tv1.column("所属デポ", anchor=tk.CENTER, width=int(self.f_size * 11))
        for f in self.v_cols[2:]: self.tv1.column(f, anchor=tk.CENTER, width=int(self.f_size * 9))

        # Tab 2
        self.h2 = tk.Frame(self.t2, bg=CCARD); self.h2.pack(fill=tk.X, padx=15, pady=8)
        self.h2_top = tk.Frame(self.h2, bg=CCARD); self.h2_top.pack(fill=tk.X, pady=(0, 5))
        self.h2_bottom = tk.Frame(self.h2, bg=CCARD); self.h2_bottom.pack(fill=tk.X)
        
        tk.Label(self.h2_bottom, text="デポ:", bg=CCARD, font=self.fb).pack(side=tk.LEFT, padx=2)
        self.t2_dep = ttk.Combobox(self.h2_bottom, state="readonly", font=self.fn, width=12); self.t2_dep.pack(side=tk.LEFT, padx=2); self.t2_dep.bind("<<ComboboxSelected>>", self.on_t2_dep)
        tk.Label(self.h2_bottom, text="Dr.:", bg=CCARD, font=self.fb).pack(side=tk.LEFT, padx=2)
        self.t2_drv = ttk.Combobox(self.h2_bottom, state="readonly", font=self.fn, width=14); self.t2_drv.pack(side=tk.LEFT, padx=2); self.t2_drv.bind("<<ComboboxSelected>>", self.on_t2_drv_selected)
        
        self.btn_multi_drv = tk.Button(self.h2_bottom, text="複数", font=self.fs, command=self.pop_multi_drv)
        self.btn_multi_drv.pack(side=tk.LEFT, padx=(0, 2))
        
        tk.Label(self.h2_bottom, text="項目:", bg=CCARD, font=self.fb).pack(side=tk.LEFT, padx=2)
        
        self.t2_itm = ttk.Combobox(self.h2_bottom, state="readonly", values=self.num_f, font=self.fn, width=12)
        self.t2_itm.pack(side=tk.LEFT, padx=2)
        self.t2_itm.current(0)
        self.t2_itm.bind("<<ComboboxSelected>>", self.on_t2_itm_selected)
        
        self.btn_multi = tk.Button(self.h2_bottom, text="☑ 複数・比較", font=self.fs, command=self.pop_multi)
        self.btn_multi.pack(side=tk.LEFT, padx=(2, 10))
        
        tk.Button(self.h2_bottom, text="📅 日別", font=self.fb, command=lambda: self.set_u("day")).pack(side=tk.LEFT, padx=2)
        tk.Button(self.h2_bottom, text="🌙 月別", font=self.fb, command=lambda: self.set_u("month")).pack(side=tk.LEFT, padx=2)
        
        self.b2_tg = tk.Button(self.h2_bottom, text="🚨 不良表示", font=self.fb, bg="#ffc107", fg="#000000", command=self.tg_b2)
        self.b2_tg.pack(side=tk.LEFT, padx=10)
        
        # ★追加：画像一覧ボタン
        self.btn_img_list = tk.Button(self.h2_bottom, text="🖼️ 画像一覧", font=self.fb, bg="#17a2b8", fg="white", command=self.pop_image_list)
        self.btn_img_list.pack(side=tk.LEFT, padx=5)
        
        self.l2_avg = tk.Label(self.h2_bottom, text="平均: --", bg=CCARD, fg=CPRI, font=self.ft); self.l2_avg.pack(side=tk.RIGHT, padx=10)
        
        self.m2_pw = tk.PanedWindow(self.t2, orient=tk.VERTICAL, sashwidth=8, sashrelief=tk.GROOVE, bg=CBG)
        self.m2_pw.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)
        
        f2_tbl = tk.Frame(self.m2_pw, bg=CCARD)
        self.m2_pw.add(f2_tbl, minsize=100)
        
        self.tv2 = ttk.Treeview(f2_tbl, columns=("d", "w", "v", "vw", "vtf"), show="headings")
        s2y, s2x = ttk.Scrollbar(f2_tbl, orient=tk.VERTICAL, command=self.tv2.yview), ttk.Scrollbar(f2_tbl, orient=tk.HORIZONTAL, command=self.tv2.xview)
        self.tv2.configure(yscrollcommand=s2y.set, xscrollcommand=s2x.set); s2x.pack(side=tk.BOTTOM, fill=tk.X); s2y.pack(side=tk.RIGHT, fill=tk.Y); self.tv2.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        for k, v in zip(("d", "w", "v", "vw", "vtf"), ("日付", "曜日", "実績", "週平均比較", "火～金比較")): self.tv2.heading(k, text=v)

        c2_f = tk.Frame(self.m2_pw, bg=CCARD, bd=1, relief=tk.GROOVE)
        self.m2_pw.add(c2_f, minsize=200)
        
        ttop = tk.Frame(c2_f, bg=CCARD); ttop.pack(fill=tk.X, padx=5, pady=(5,0))
        tk.Label(ttop, text="※ 不良表示時は赤いバーにカーソルを合わせると内訳がポップアップします", bg=CCARD, font=self.fs, fg="#6c757d").pack(side=tk.LEFT, padx=5)

        self.f2, self.a2 = plt.subplots(figsize=(8, 2.5), facecolor=CCARD); self.a2.set_facecolor(CCARD)
        self.cv2 = FigureCanvasTkAgg(self.f2, master=c2_f); self.cv2.get_tk_widget().pack(fill=tk.BOTH, expand=True, padx=5, pady=(0,5))
        self.root.after(300, lambda: self.m2_pw.sash_place(0, 0, int(self.f_size * 2.4 * 6)))

        # Tab 3
        self.h3 = tk.Frame(self.t3, bg=CCARD); self.h3.pack(fill=tk.X, padx=15, pady=8)
        self.h3_top = tk.Frame(self.h3, bg=CCARD); self.h3_top.pack(fill=tk.X, pady=(0, 5))
        self.h3_bottom = tk.Frame(self.h3, bg=CCARD); self.h3_bottom.pack(fill=tk.X)
        
        self.bf_dp, self.bf_cl, self.bf_rs = [ttk.Combobox(self.h3_bottom, state="readonly", font=self.fn, width=w) for w in (12,12,12)]
        self.bf_dr = tk.Entry(self.h3_bottom, font=self.fn, bd=1, relief=tk.SOLID, width=12)
        for lbl, cb in [("デポ:", self.bf_dp), ("荷主:", self.bf_cl), ("原因:", self.bf_rs)]:
            tk.Label(self.h3_bottom, text=lbl, bg=CCARD, font=self.fb).pack(side=tk.LEFT, padx=(0,2)); cb.pack(side=tk.LEFT, padx=(0,5)); cb.bind("<<ComboboxSelected>>", lambda e: self.request_ref_bad())
        tk.Label(self.h3_bottom, text="ﾄﾞﾗｲﾊﾞｰ:", bg=CCARD, font=self.fb).pack(side=tk.LEFT, padx=(0,2)); self.bf_dr.pack(side=tk.LEFT, padx=(0,5)); self.bf_dr.bind("<KeyRelease>", lambda e: self.request_ref_bad())
        tk.Button(self.h3_bottom, text="リセット", font=self.fs, command=self.clr_bflt).pack(side=tk.LEFT, padx=(0, 20))
        tk.Button(self.h3_bottom, text="➕ 手入力追加", font=self.fb, bg=CACC, fg="white", command=self.pop_add_bad).pack(side=tk.RIGHT, padx=5)
        tk.Label(self.t3, text="※ リストを選択してCtrl+C（右クリック）でコピーできます / 行をワンクリックで編集・削除", bg=CCARD, font=self.fn, fg="#6c757d").pack(anchor=tk.W, padx=25, pady=(0, 5))

        self.m3_pw = tk.PanedWindow(self.t3, orient=tk.VERTICAL, sashwidth=8, sashrelief=tk.GROOVE, bg=CBG)
        self.m3_pw.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)
        
        b_tbl = tk.Frame(self.m3_pw, bg=CCARD)
        self.m3_pw.add(b_tbl, minsize=100)
        self.tv4 = ttk.Treeview(b_tbl, columns=self.b_cols, show="headings")
        sby, sbx = ttk.Scrollbar(b_tbl, orient=tk.VERTICAL, command=self.tv4.yview), ttk.Scrollbar(b_tbl, orient=tk.HORIZONTAL, command=self.tv4.xview)
        self.tv4.configure(yscrollcommand=sby.set, xscrollcommand=sbx.set); sbx.pack(side=tk.BOTTOM, fill=tk.X); sby.pack(side=tk.RIGHT, fill=tk.Y); self.tv4.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.tv4.bind("<ButtonRelease-1>", self.on_tv4_click)
        
        for c in self.b_cols: self.tv4.heading(c, text=c)
        for c in self.b_cols: self.tv4.column(c, anchor=tk.W if c in ["荷主名称", "問合せ中分類"] else tk.CENTER, width=int(self.f_size * 12))
        
        c3_f = tk.Frame(self.m3_pw, bg=CCARD, bd=1, relief=tk.GROOVE)
        self.m3_pw.add(c3_f, minsize=200)
        self.f4, self.a4 = plt.subplots(figsize=(8, 3.0), facecolor=CCARD); self.cv4 = FigureCanvasTkAgg(self.f4, master=c3_f); self.cv4.get_tk_widget().pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        self.root.after(300, lambda: self.m3_pw.sash_place(0, 0, int(self.f_size * 2.4 * 6)))
        
        # Tab 4 (e-ラーニング)
        self.h4 = tk.Frame(self.t4, bg=CCARD); self.h4.pack(fill=tk.X, padx=15, pady=8)
        self.h4_top = tk.Frame(self.h4, bg=CCARD); self.h4_top.pack(fill=tk.X, pady=(0, 5))
        self.h4_bottom = tk.Frame(self.h4, bg=CCARD); self.h4_bottom.pack(fill=tk.X)
        
        tk.Button(self.h4_bottom, text="📁 e-ラーニングCSV読込", bg=CPRI, fg="white", font=self.fb, command=self.ld_elearning).pack(side=tk.LEFT, padx=5)
        tk.Button(self.h4_bottom, text="📊 e-ラーニングExcel読込", bg="#28a745", fg="white", font=self.fb, command=self.ld_elearning_excel).pack(side=tk.LEFT, padx=5)
        tk.Label(self.h4_bottom, text="デポ絞り込:", bg=CCARD, font=self.fb).pack(side=tk.LEFT, padx=(20, 5))
        self.t4_dep = ttk.Combobox(self.h4_bottom, state="readonly", font=self.fn, width=15)
        self.t4_dep.pack(side=tk.LEFT)
        self.t4_dep.bind("<<ComboboxSelected>>", lambda e: self.upd_tab4())
        
        tk.Label(self.h4_bottom, text="項目絞り込:", bg=CCARD, font=self.fb).pack(side=tk.LEFT, padx=(20, 5))
        self.t4_itm = ttk.Combobox(self.h4_bottom, state="readonly", font=self.fn, width=20)
        self.t4_itm.pack(side=tk.LEFT)
        self.t4_itm.bind("<<ComboboxSelected>>", lambda e: self.upd_tab4())
        
        tk.Label(self.t4, text="※ リストを選択してCtrl+C（右クリック）でコピーできます / グラフのバーをクリックで手動完了", bg=CBG, font=self.fs, fg="#6c757d").pack(anchor=tk.W, padx=25, pady=(0, 2))
        
        self.m4_pw = tk.PanedWindow(self.t4, orient=tk.VERTICAL, sashwidth=8, sashrelief=tk.GROOVE, bg=CBG)
        self.m4_pw.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)
        
        f4_tbl = tk.Frame(self.m4_pw, bg=CCARD)
        self.m4_pw.add(f4_tbl, minsize=100)
        self.tv_el = ttk.Treeview(f4_tbl, show="headings")
        scr4y = ttk.Scrollbar(f4_tbl, orient=tk.VERTICAL, command=self.tv_el.yview)
        scr4x = ttk.Scrollbar(f4_tbl, orient=tk.HORIZONTAL, command=self.tv_el.xview)
        self.tv_el.configure(yscrollcommand=scr4y.set, xscrollcommand=scr4x.set)
        scr4x.pack(side=tk.BOTTOM, fill=tk.X); scr4y.pack(side=tk.RIGHT, fill=tk.Y)
        self.tv_el.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        c4_f = tk.Frame(self.m4_pw, bg=CCARD, bd=1, relief=tk.GROOVE)
        self.m4_pw.add(c4_f, minsize=200)
        self.f_el, self.a_el = plt.subplots(figsize=(8, 2.5), facecolor=CCARD)
        self.cv_el = FigureCanvasTkAgg(self.f_el, master=c4_f)
        self.cv_el.get_tk_widget().pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

        self.root.after(300, lambda: self.m4_pw.sash_place(0, 0, int(self.f_size * 2.4 * 5)))

        # Tab 5 (SBS追跡)
        self.h5 = tk.Frame(self.t5, bg=CCARD); self.h5.pack(fill=tk.X, padx=15, pady=8)
        
        self.t5_top = tk.Frame(self.h5, bg=CCARD)
        self.t5_top.pack(fill=tk.X, pady=2)
        tk.Label(self.t5_top, text="SBS お荷物お問い合わせ (最大100件まで複数行ペースト対応):", bg=CCARD, font=self.fb, fg=CPRI).pack(side=tk.LEFT)
        
        # --- ここから右側に「アプリボタン」と「エラー対策ボタン」を配置 ---
        t5_right_frame = tk.Frame(self.t5_top, bg=CCARD)
        t5_right_frame.pack(side=tk.RIGHT, padx=5)
        
        t5_app_frame = tk.Frame(t5_right_frame, bg=CCARD)
        t5_app_frame.pack(side=tk.TOP, fill=tk.X)
        
        self.btn_iphone = tk.Button(t5_app_frame, text="📱 iPhoneアプリ", font=self.fb, bg="#000000", fg="white", relief=tk.FLAT, command=lambda: webbrowser.open("https://apps.apple.com/jp/app/scan-to-note/id602515377"))
        self.btn_iphone.pack(side=tk.RIGHT, padx=(5, 0))

        self.btn_android = tk.Button(t5_app_frame, text="📱 Androidアプリ", font=self.fb, bg="#3DDC84", fg="white", relief=tk.FLAT, command=lambda: webbrowser.open("https://play.google.com/store/apps/details?id=com.berrywing.scantonote&hl=ja"))
        self.btn_android.pack(side=tk.RIGHT, padx=5)
        
        def _show_driver_help():
            hp = tk.Toplevel(self.root)
            hp.title("⚠️ エラー解消手順: Edgeドライバーの手動追加")
            hp.geometry("800x650")
            hp.configure(bg=CBG)
            hp.transient(self.root)
            hp.grab_set()

            tk.Label(hp, text="🚨 Edgeドライバーの手動追加手順", font=self.ft, bg=CBG, fg="#dc3545").pack(pady=(15, 5))
            
            msg = (
                "1️⃣ 今のEdgeの「バージョン」を確認する\n"
                "まず、お使いのPCのEdgeのバージョンを調べます。\n"
                "Edgeブラウザを開きます。\n"
                "画面右上の「…」（設定など）をクリックします。\n"
                "一番下の「ヘルプとフィードバック」から「Microsoft Edge について」をクリックします。\n"
                "画面の真ん中に 「バージョン 126.0.2592.87 (公式ビルド)」 のような数字が表示されます。\n"
                "この 最初の数字（この例なら 126） を覚えておきます。\n\n"
                "2️⃣ ページから同じバージョンを探す\n"
                "ダウンロードページを少し下にスクロールすると、バージョンの数字が箇条書きで並んでいる場所があります。\n"
                "そこで、先ほど調べた数字（例：126）から始まるバージョンを探してください。\n"
                "（※通常は「安定チャネル (Stable Channel)」というところに最新版があります）\n\n"
                "3️⃣ 「x64」をクリックしてダウンロードする\n"
                "該当するバージョンを見つけたら、そのすぐ下にリンクがいくつか並んでいます。\n"
                "（x86 / x64 / Mac / Linux / ARM64 など）\n"
                "一般的な会社のWindows PCであれば、迷わず 「x64」 のリンクをクリックしてください。\n"
                "クリックすると、ZIPファイル（圧縮ファイル）のダウンロードが始まります。\n\n"
                "4️⃣ 解凍して、名前を変えて、フォルダに入れる\n"
                "ダウンロードしたZIPファイルを右クリックし、「すべて展開（解凍）」します。\n"
                "解凍されたフォルダの中に msedgedriver.exe というファイルが入っています。\n"
                "このファイルの名前を、手順1で調べた数字をつけて msedgedriver_126.exe （バージョンが126の場合）に変更します。\n"
                "変更したファイルを、ご自身のアプリ（EXE）と同じ場所にある drivers フォルダ の中にポイッと入れれば準備完了です！"
            )
            
            txt_frame = tk.Frame(hp, bg=CCARD, bd=1, relief=tk.SOLID)
            txt_frame.pack(fill=tk.BOTH, expand=True, padx=20, pady=5)
            
            scr = ttk.Scrollbar(txt_frame, orient=tk.VERTICAL)
            txt = tk.Text(txt_frame, font=self.fn, bg=CCARD, yscrollcommand=scr.set, padx=10, pady=10, wrap=tk.WORD)
            scr.config(command=txt.yview)
            scr.pack(side=tk.RIGHT, fill=tk.Y)
            txt.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
            
            txt.insert(tk.END, msg)
            txt.config(state=tk.DISABLED) # テキストを編集不可にする

            btn_frame = tk.Frame(hp, bg=CBG)
            btn_frame.pack(fill=tk.X, padx=20, pady=15)
            
            tk.Button(btn_frame, text="✖ 閉じる", bg="#6c757d", fg="white", font=self.fb, command=hp.destroy).pack(side=tk.LEFT, expand=True, fill=tk.X, padx=5)
            tk.Button(btn_frame, text="🌐 公式ダウンロードページを開く", bg=CPRI, fg="white", font=self.fb, command=lambda: webbrowser.open("https://developer.microsoft.com/ja-jp/microsoft-edge/tools/webdriver/")).pack(side=tk.RIGHT, expand=True, fill=tk.X, padx=5)

        self.btn_err_help = tk.Button(t5_right_frame, text="⚠️ エラーが出たらこちら", font=self.fs, bg="#dc3545", fg="white", relief=tk.FLAT, command=_show_driver_help)
        self.btn_err_help.pack(side=tk.TOP, fill=tk.X, pady=(2, 0))
        # ------------------------------------------------------------------

        self.t5_input_frame = tk.Frame(self.h5, bg=CCARD)
        self.t5_input_frame.pack(fill=tk.X, pady=2)
        
        self.t5_txt_scroll = ttk.Scrollbar(self.t5_input_frame, orient=tk.VERTICAL)
        self.t5_txt = tk.Text(self.t5_input_frame, font=self.fn, width=25, height=5, bd=1, relief=tk.SOLID, yscrollcommand=self.t5_txt_scroll.set)
        self.t5_txt.pack(side=tk.LEFT, fill=tk.Y, pady=2)
        self.t5_txt_scroll.config(command=self.t5_txt.yview)
        self.t5_txt_scroll.pack(side=tk.LEFT, fill=tk.Y, pady=2)
        
        # --- ここを追加：右クリック即貼り付け機能 ---
        def _right_click_paste(event):
            try:
                # パソコンが現在記憶しているコピー内容(クリップボード)を取得
                clipboard_text = self.root.clipboard_get()
                # 枠の中身を一度すべて消去する
                self.t5_txt.delete("1.0", tk.END)
                # コピーしていた内容を枠に直接書き込む
                self.t5_txt.insert("1.0", clipboard_text)
            except tk.TclError:
                # クリップボードが空だったり、画像等テキスト以外だった場合は何もしない
                pass 
                
        # 右クリック（Button-3）をした時に、上記の機能を呼び出す設定
        self.t5_txt.bind("<Button-3>", _right_click_paste)
        # --------------------------------------------
        
        t5_btn_frame = tk.Frame(self.t5_input_frame, bg=CCARD)
        t5_btn_frame.pack(side=tk.LEFT, padx=15, fill=tk.Y)
        
        self.t5_btn = tk.Button(t5_btn_frame, text="🔍 追跡開始", bg=CACC, fg="white", font=self.fb, command=self.run_sbs_tracking, width=15)
        self.t5_btn.pack(side=tk.TOP, pady=5)
        self.t5_lbl_status = tk.Label(t5_btn_frame, text="左の枠にA0417...Aの形式で\n複数行貼り付けてください\n(自動で数字のみ抽出します)", bg=CCARD, font=self.fn, fg="#6c757d", justify=tk.LEFT)
        self.t5_lbl_status.pack(side=tk.TOP)

        # Tab 5 Treeview
        t5_f = tk.Frame(self.t5, bg=CCARD)
        t5_f.pack(fill=tk.BOTH, expand=True, padx=15, pady=(0, 15))
        self.tv_sbs = ttk.Treeview(t5_f, show="headings")
        scr5y = ttk.Scrollbar(t5_f, orient=tk.VERTICAL, command=self.tv_sbs.yview)
        scr5x = ttk.Scrollbar(t5_f, orient=tk.HORIZONTAL, command=self.tv_sbs.xview)
        self.tv_sbs.configure(yscrollcommand=scr5y.set, xscrollcommand=scr5x.set)
        scr5x.pack(side=tk.BOTTOM, fill=tk.X); scr5y.pack(side=tk.RIGHT, fill=tk.Y)
        self.tv_sbs.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        # --- 全Treeviewに対するコピー機能(Ctrl+C / 右クリック)のバインド ---
        for tv in [self.tv1, self.tv2, self.tv4, self.tv_el, self.tv_sbs]:
            tv.bind("<Control-c>", self.copy_treeview_selection)
            tv.bind("<Command-c>", self.copy_treeview_selection)
            tv.bind("<Button-3>", self.show_context_menu)
            
        self.on_tab_change()

# ★追加：画像登録ポップアップ
    def pop_reg_img(self):
        if not globals().get('PILLOW_AVAILABLE', False):
            messagebox.showerror("エラー", "画像機能を使用するには Pillow ライブラリが必要です。\nコマンドプロンプトで pip install Pillow を実行してください。")
            return
            
        p = tk.Toplevel(self.root)
        p.title("📸 グラフ用 画像登録")
        p.geometry("500x320")
        p.configure(bg=CBG)
        p.transient(self.root)
        p.grab_set()
        
        f_top = tk.Frame(p, bg=CBG)
        f_top.pack(fill=tk.X, padx=20, pady=(20, 10))
        
        tk.Label(f_top, text="対象年月:", bg=CBG, font=self.fb).grid(row=0, column=0, sticky="w", pady=10)
        
        y_cb = ttk.Combobox(f_top, state="readonly", values=[f"{y}年" for y in range(2020, 2031)], width=10, font=self.fn)
        y_cb.grid(row=0, column=1, padx=5, pady=10)
        y_cb.set(f"{datetime.now().year}年")
        
        m_cb = ttk.Combobox(f_top, state="readonly", values=[f"{m}月" for m in range(1, 13)], width=8, font=self.fn)
        m_cb.grid(row=0, column=2, padx=5, pady=10)
        m_cb.set(f"{datetime.now().month}月")
        
        tk.Label(f_top, text="タイトル:", bg=CBG, font=self.fb).grid(row=1, column=0, sticky="w", pady=10)
        title_ent = tk.Entry(f_top, font=self.fn, width=28)
        title_ent.grid(row=1, column=1, columnspan=2, padx=5, pady=10)
        
        def _save_img(img):
            ym = f"{y_cb.get().replace('年', '')}/{int(m_cb.get().replace('月', '')):02d}"
            title = title_ent.get().strip()
            if not title:
                title = "無題の画像"
                
            # ★アプリを消しても消えないように、画像フォルダを作ってファイルとして保存
            if getattr(sys, 'frozen', False):
                app_path = os.path.dirname(sys.executable)
            else:
                app_path = os.path.dirname(os.path.abspath(__file__))
                
            img_dir = os.path.join(app_path, "saved_images")
            os.makedirs(img_dir, exist_ok=True)
            
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            filename = f"img_{ym.replace('/', '')}_{timestamp}.png"
            filepath = os.path.join(img_dir, filename)
            
            img.save(filepath, format="PNG")
            
            if not hasattr(self, 'graph_images'):
                self.graph_images = {}
            if ym not in self.graph_images:
                self.graph_images[ym] = []
                
            self.graph_images[ym].append({
                "title": title,
                "filename": filename
            })
            self.save_db()
            self.request_upd()
            messagebox.showinfo("登録完了", f"{ym} に画像を登録しました！\nグラフ画面に青いボタンとして追加されます。")
            p.destroy()

        def _load_from_file():
            fpath = filedialog.askopenfilename(title="画像選択", filetypes=[("Image Files", "*.png *.jpg *.jpeg *.bmp")])
            if fpath:
                try:
                    img = Image.open(fpath)
                    _save_img(img)
                except Exception as e:
                    messagebox.showerror("エラー", f"画像の読み込みに失敗しました:\n{e}")

        def _load_from_clipboard(event=None):
            try:
                img = ImageGrab.grabclipboard()
                if isinstance(img, Image.Image):
                    _save_img(img)
                else:
                    messagebox.showwarning("警告", "クリップボードに画像が見つかりません。\n(Win+Shift+S 等で画面をコピーしてから再度お試しください)")
            except Exception as e:
                messagebox.showerror("エラー", f"クリップボードからの取得に失敗しました:\n{e}")

        p.bind("<Control-v>", _load_from_clipboard)
        p.bind("<Command-v>", _load_from_clipboard)
        
        f_btn = tk.Frame(p, bg=CBG)
        f_btn.pack(fill=tk.BOTH, expand=True, padx=20, pady=10)
        
        tk.Button(f_btn, text="📁 画像ファイルから選ぶ", bg=CPRI, fg="white", font=self.fb, command=_load_from_file).pack(fill=tk.X, pady=5, ipady=5)
        tk.Button(f_btn, text="📋 コピーした画像を貼り付け\n(またはこの画面で Ctrl+V を押す)", bg="#28a745", fg="white", font=self.fb, command=_load_from_clipboard).pack(fill=tk.X, pady=5, ipady=5)

    # ★追加：画像表示用ポップアップ（大画面）
    def pop_show_image(self, img_info):
        if not globals().get('PILLOW_AVAILABLE', False): return
        
        p = tk.Toplevel(self.root)
        p.title(img_info["title"])
        p.geometry("1100x800")
        p.configure(bg=CCARD)
        p.transient(self.root)
        
        f_top = tk.Frame(p, bg=CCARD)
        f_top.pack(fill=tk.X, padx=15, pady=10)
        
        lbl_title = tk.Label(f_top, text=f"📸 {img_info['title']}", font=self.ft, bg=CCARD, fg=CPRI)
        lbl_title.pack(side=tk.LEFT)
        
        def _edit_title():
            new_title = simpledialog.askstring("タイトル変更", "新しいタイトルを入力してください:", initialvalue=img_info["title"], parent=p)
            if new_title is not None:
                new_title = new_title.strip()
                if new_title:
                    img_info["title"] = new_title
                    lbl_title.config(text=f"📸 {new_title}")
                    p.title(new_title)
                    self.save_db()
                    self.request_upd()
                    
        tk.Button(f_top, text="✏️ タイトル変更", bg="#28a745", fg="white", font=self.fb, command=_edit_title).pack(side=tk.LEFT, padx=15)
        
        def _del():
            if messagebox.askyesno("削除確認", "この画像を削除しますか？\n（この操作は元に戻せません）"):
                for ym, arr in self.graph_images.items():
                    if img_info in arr:
                        arr.remove(img_info)
                        
                        if "filename" in img_info:
                            try:
                                if getattr(sys, 'frozen', False):
                                    app_path = os.path.dirname(sys.executable)
                                else:
                                    app_path = os.path.dirname(os.path.abspath(__file__))
                                filepath = os.path.join(app_path, "saved_images", img_info["filename"])
                                if os.path.exists(filepath):
                                    os.remove(filepath)
                            except:
                                pass
                                
                        self.save_db()
                        self.request_upd()
                        break
                p.destroy()
        
        tk.Button(f_top, text="🗑️ この画像を削除", bg="#dc3545", fg="white", font=self.fb, command=_del).pack(side=tk.RIGHT)
        
        cv = tk.Canvas(p, bg=CCARD)
        scr_y = ttk.Scrollbar(p, orient=tk.VERTICAL, command=cv.yview)
        scr_x = ttk.Scrollbar(p, orient=tk.HORIZONTAL, command=cv.xview)
        cv.configure(yscrollcommand=scr_y.set, xscrollcommand=scr_x.set)
        scr_x.pack(side=tk.BOTTOM, fill=tk.X)
        scr_y.pack(side=tk.RIGHT, fill=tk.Y)
        cv.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        
        try:
            # 互換性維持（古いBase64データの場合）
            if "b64" in img_info:
                img_data = base64.b64decode(img_info["b64"])
                img = Image.open(io.BytesIO(img_data))
            else:
                if getattr(sys, 'frozen', False):
                    app_path = os.path.dirname(sys.executable)
                else:
                    app_path = os.path.dirname(os.path.abspath(__file__))
                filepath = os.path.join(app_path, "saved_images", img_info["filename"])
                
                if not os.path.exists(filepath):
                    messagebox.showerror("エラー", "画像ファイルが見つかりません。\n削除または移動された可能性があります。")
                    p.destroy()
                    return
                img = Image.open(filepath)
            
            p.photo = ImageTk.PhotoImage(img)
            cv.create_image(0, 0, anchor="nw", image=p.photo)
            cv.configure(scrollregion=(0, 0, img.width, img.height))
            
            def _on_mousewheel(e):
                cv.yview_scroll(int(-1 * (e.delta / 120)), "units")
            p.bind_all("<MouseWheel>", _on_mousewheel)
            p.bind("<Destroy>", lambda e: p.unbind_all("<MouseWheel>") if e.widget == p else None)
            
        except Exception as e:
            messagebox.showerror("エラー", f"画像の表示に失敗しました:\n{e}")

# ★追加：画像一覧表示ポップアップ
    def pop_image_list(self):
        p = tk.Toplevel(self.root)
        p.title("🖼️ 保存した画像一覧")
        # 前回のウィンドウサイズ・位置を復元する
        p.geometry(getattr(self, 'img_list_geo', "900x600"))
        p.configure(bg=CBG)
        p.transient(self.root)
        p.grab_set()
        
        # ウィンドウを閉じる時に現在のサイズ・位置を保存する
        def _on_close():
            self.img_list_geo = p.geometry()
            self.save_db()
            p.destroy()
            
        p.protocol("WM_DELETE_WINDOW", _on_close)
        
        tk.Label(p, text="保存されている画像一覧", font=self.ft, bg=CBG, fg=CPRI).pack(pady=10)
        
        # 内部処理用に隠し列(idx)を持たせる
        tv = ttk.Treeview(p, columns=("ym", "title", "idx"), show="headings")
        tv.heading("ym", text="対象年月")
        tv.heading("title", text="タイトル")
        tv.column("ym", width=120, anchor=tk.CENTER)
        tv.column("title", width=730, anchor=tk.W)
        tv.column("idx", width=0, stretch=False)
        
        scr_y = ttk.Scrollbar(p, orient=tk.VERTICAL, command=tv.yview)
        tv.configure(yscrollcommand=scr_y.set)
        scr_y.pack(side=tk.RIGHT, fill=tk.Y)
        tv.pack(fill=tk.BOTH, expand=True, padx=20, pady=10)
        
        def _refresh_list():
            for item in tv.get_children():
                tv.delete(item)
            has_d = False
            if hasattr(self, 'graph_images'):
                for y_m in sorted(self.graph_images.keys(), reverse=True):
                    for i_x, i_info in enumerate(self.graph_images[y_m]):
                        tv.insert("", tk.END, values=(y_m, i_info["title"], i_x))
                        has_d = True
            if not has_d:
                tv.insert("", tk.END, values=("--", "保存された画像はありません", ""))

        _refresh_list()
        
        # ★下部に直接タイトルを編集できる入力枠を追加（ポップアップ回避）
        edit_frame = tk.Frame(p, bg=CBG)
        edit_frame.pack(fill=tk.X, padx=20, pady=5)
        
        tk.Label(edit_frame, text="選択中のタイトル:", bg=CBG, font=self.fb).pack(side=tk.LEFT)
        title_ent = tk.Entry(edit_frame, font=self.fn, width=50)
        title_ent.pack(side=tk.LEFT, padx=10)

        # 行を選択したときにタイトルを入力枠にセットする
        def _on_select(event):
            s = tv.selection()
            if s:
                item_vals = tv.item(s[0], "values")
                ym = item_vals[0]
                if ym != "--":
                    title_ent.delete(0, tk.END)
                    title_ent.insert(0, item_vals[1])
                    
        tv.bind("<<TreeviewSelect>>", _on_select)
        
        def _edit_list_title():
            s = tv.selection()
            if not s:
                return messagebox.showwarning("警告", "変更する行を選択してください。", parent=p)
            item_vals = tv.item(s[0], "values")
            ym = item_vals[0]
            if ym == "--": return
            idx = int(item_vals[2])
            
            new_title = title_ent.get().strip()
            if not new_title:
                return messagebox.showwarning("警告", "新しいタイトルを入力してください。", parent=p)
            
            if hasattr(self, 'graph_images') and ym in self.graph_images:
                if idx < len(self.graph_images[ym]):
                    self.graph_images[ym][idx]["title"] = new_title
                    self.save_db()
                    self.request_upd()
                    _refresh_list()
                    title_ent.delete(0, tk.END)
                    messagebox.showinfo("変更完了", "タイトルを変更しました。", parent=p)
                            
        def _del_list_item():
            s = tv.selection()
            if not s:
                return messagebox.showwarning("警告", "削除する行を選択してください。", parent=p)
            item_vals = tv.item(s[0], "values")
            ym = item_vals[0]
            if ym == "--": return
            idx = int(item_vals[2])
            
            if messagebox.askyesno("削除確認", "選択した画像を削除しますか？\n（この操作は元に戻せません）", parent=p):
                if hasattr(self, 'graph_images') and ym in self.graph_images:
                    if idx < len(self.graph_images[ym]):
                        img_info = self.graph_images[ym][idx]
                        self.graph_images[ym].pop(idx)
                        
                        if "filename" in img_info:
                            try:
                                if getattr(sys, 'frozen', False):
                                    app_path = os.path.dirname(sys.executable)
                                else:
                                    app_path = os.path.dirname(os.path.abspath(__file__))
                                filepath = os.path.join(app_path, "saved_images", img_info["filename"])
                                if os.path.exists(filepath):
                                    os.remove(filepath)
                            except:
                                pass
                                
                        self.save_db()
                        self.request_upd()
                        _refresh_list()
                        title_ent.delete(0, tk.END)

        bf = tk.Frame(p, bg=CBG)
        bf.pack(fill=tk.X, padx=20, pady=(5, 15))
        tk.Button(bf, text="✏️ タイトル変更", bg="#28a745", fg="white", font=self.fb, command=_edit_list_title).pack(side=tk.LEFT, expand=True, fill=tk.X, padx=5)
        tk.Button(bf, text="🗑️ 削除", bg="#dc3545", fg="white", font=self.fb, command=_del_list_item).pack(side=tk.LEFT, expand=True, fill=tk.X, padx=5)

    def copy_treeview_selection(self, event=None, tv=None):
        target_tv = tv if tv else event.widget
        if not isinstance(target_tv, ttk.Treeview): return
        selected = target_tv.selection()
        if not selected: return
        lines = []
        for item in selected:
            vals = target_tv.item(item, "values")
            lines.append("\t".join(str(v) for v in vals))
        if lines:
            self.root.clipboard_clear()
            self.root.clipboard_append("\n".join(lines))
            try:
                x, y = self.root.winfo_pointerx(), self.root.winfo_pointery()
                self.tooltip.show(x + 15, y + 15, f"📋 {len(selected)}行 コピーしました")
                self.root.after(1500, self.tooltip.hide)
            except: pass

    def show_context_menu(self, event):
        tv = event.widget
        if not isinstance(tv, ttk.Treeview): return
        item = tv.identify_row(event.y)
        if item and item not in tv.selection():
            tv.selection_set(item)
        if not tv.selection(): return
        menu = tk.Menu(self.root, tearoff=0, font=self.fn)
        menu.add_command(label="📋 選択行をコピー (Ctrl+C)", command=lambda: self.copy_treeview_selection(tv=tv))
        menu.post(event.x_root, event.y_root)
        
    def on_tv4_click(self, event):
        region = self.tv4.identify("region", event.x, event.y)
        if region == "cell":
            self.pop_edit_bad(event)

    def on_popup_tv_click(self, event, tv, p):
        region = tv.identify("region", event.x, event.y)
        if region == "cell":
            self.pop_edit_bad(event, tv, p)

    def pop_edit_bad(self, event, treeview=None, parent_dialog=None):
        tv = treeview if treeview else self.tv4
        s = tv.selection()
        if not s: return
        vals = tv.item(s[0], "values")
        if not vals or len(vals) < 5: return
        
        v_dt, v_dp, v_dr, v_cl, v_rs = vals
        
        p = tk.Toplevel(self.root)
        p.title("🚨 不良配送 編集・削除")
        p.geometry("500x350")
        p.configure(bg=CBG)
        p.transient(self.root)
        p.grab_set()
        
        pf = tk.Frame(p, bg=CBG, padx=20, pady=20)
        pf.pack(fill=tk.BOTH, expand=True)

        tk.Label(pf, text="配送日 (YYYY/MM/DD):", bg=CBG, font=self.fb).grid(row=0, column=0, sticky="w", pady=5)
        e_dt = tk.Entry(pf, font=self.fn, bd=1, relief=tk.SOLID, width=20)
        e_dt.insert(0, v_dt)
        e_dt.grid(row=0, column=1, pady=5)

        tk.Label(pf, text="デポ名:", bg=CBG, font=self.fb).grid(row=1, column=0, sticky="w", pady=5)
        e_dp = tk.Entry(pf, font=self.fn, bd=1, relief=tk.SOLID, width=20)
        e_dp.insert(0, v_dp)
        e_dp.grid(row=1, column=1, pady=5)

        tk.Label(pf, text="ドライバ名:", bg=CBG, font=self.fb).grid(row=2, column=0, sticky="w", pady=5)
        e_dr = tk.Entry(pf, font=self.fn, bd=1, relief=tk.SOLID, width=20)
        e_dr.insert(0, v_dr)
        e_dr.grid(row=2, column=1, pady=5)

        tk.Label(pf, text="荷主名称:", bg=CBG, font=self.fb).grid(row=3, column=0, sticky="w", pady=5)
        e_cl = tk.Entry(pf, font=self.fn, bd=1, relief=tk.SOLID, width=20)
        e_cl.insert(0, v_cl)
        e_cl.grid(row=3, column=1, pady=5)

        tk.Label(pf, text="問合せ中分類 (原因):", bg=CBG, font=self.fb).grid(row=4, column=0, sticky="w", pady=5)
        e_rs = tk.Entry(pf, font=self.fn, bd=1, relief=tk.SOLID, width=20)
        e_rs.insert(0, v_rs)
        e_rs.grid(row=4, column=1, pady=5)
        
        def _find_and_delete_old():
            for k, df in self.bad_delivery_data.items():
                if df.empty: continue
                for idx, row in df.iterrows():
                    rdt_val = str(row.get("配送日"))
                    m = re.search(r'(\d{4}[-/]\d{1,2}[-/]\d{1,2})', rdt_val)
                    ext_val = m.group(1) if m else rdt_val
                    try:
                        r_dt = pd.to_datetime(ext_val).strftime("%Y/%m/%d")
                    except:
                        r_dt = rdt_val
                        
                    r_dp = self.cln_dep(row.get("デポ名", ""))
                    r_dr = str(row.get("ドライバ名", ""))
                    r_cl = str(row.get("荷主名称", ""))
                    r_rs = str(row.get("問合せ中分類", ""))
                    
                    if r_dt == v_dt and r_dp == v_dp and r_dr == v_dr and r_cl == v_cl and r_rs == v_rs:
                        self.bad_delivery_data[k] = df.drop(idx)
                        return True
            return False

        def _save():
            new_dt, new_dp, new_dr, new_cl, new_rs = e_dt.get().strip(), e_dp.get().strip(), e_dr.get().strip(), e_cl.get().strip(), e_rs.get().strip()
            
            if not new_dt or not new_dp or not new_dr or not new_cl or not new_rs:
                return messagebox.showwarning("警告", "すべての項目を入力してください")
            try:
                new_dt = pd.to_datetime(new_dt).strftime("%Y/%m/%d")
            except:
                return messagebox.showwarning("警告", "配送日は正しい形式 (YYYY/MM/DD) で入力してください")
                
            if not _find_and_delete_old():
                return messagebox.showwarning("エラー", "元のデータが見つからないため更新できません。")
                
            df_new = pd.DataFrame([{"配送日": new_dt, "デポ名": new_dp, "ドライバ名": new_dr, "荷主名称": new_cl, "問合せ中分類": new_rs}])
            for c in self.b_cols:
                if c not in df_new.columns: df_new[c] = ""
            df_new = df_new[self.b_cols].astype(str)
            
            if "manual_added" in self.bad_delivery_data:
                self.bad_delivery_data["manual_added"] = pd.concat([self.bad_delivery_data["manual_added"], df_new], ignore_index=True)
            else:
                self.bad_delivery_data["manual_added"] = df_new
                
            self.save_db()
            self._update_cache()
            self.request_ref_bad()
            self.request_upd()
            p.destroy()
            if parent_dialog: parent_dialog.destroy()
            messagebox.showinfo("更新完了", "データを更新しました。")

        def _delete():
            if messagebox.askyesno("確認", "この不良配送データを削除しますか？\n（手入力・CSV読込分に関わらず取り消されます）"):
                if _find_and_delete_old():
                    self.save_db()
                    self._update_cache()
                    self.request_ref_bad()
                    self.request_upd()
                    p.destroy()
                    if parent_dialog: parent_dialog.destroy()
                    messagebox.showinfo("削除完了", "データを削除しました。")
                else:
                    messagebox.showwarning("エラー", "元のデータが見つかりませんでした。")
                    
        bf = tk.Frame(p, bg=CBG)
        bf.pack(side=tk.BOTTOM, fill=tk.X, pady=20, padx=20)
        
        tk.Button(bf, text="🗑️ 削除", bg="#dc3545", fg="white", font=self.fb, command=_delete).pack(side=tk.LEFT, expand=True, fill=tk.X, padx=5)
        tk.Button(bf, text="💾 変更を保存", bg=CPRI, fg="white", font=self.fb, command=_save).pack(side=tk.LEFT, expand=True, fill=tk.X, padx=5)

    def pop_bad_list_for_date(self, dt, graph_df):
        det = graph_df[graph_df["配送月"] == dt] if len(dt) == 7 and "配送月" in graph_df.columns else graph_df[graph_df["配送日"].str.startswith(dt)] if len(dt) == 7 else graph_df[graph_df["配送日"] == dt]
        if det.empty: return
        
        p = tk.Toplevel(self.root)
        p.title(f"🚨 {dt} の不良配送一覧")
        p.geometry("800x400")
        p.configure(bg=CBG)
        p.transient(self.root)
        p.grab_set()
        
        tk.Label(p, text=f"【{dt}】 不良配送データ", font=self.ft, bg=CBG, fg=CPRI).pack(pady=10)
        tk.Label(p, text="※編集・削除したい行をワンクリックしてください", font=self.fs, bg=CBG, fg="#6c757d").pack(pady=5)
        
        tv = ttk.Treeview(p, columns=self.b_cols, show="headings")
        scr_y = ttk.Scrollbar(p, orient=tk.VERTICAL, command=tv.yview)
        tv.configure(yscrollcommand=scr_y.set)
        scr_y.pack(side=tk.RIGHT, fill=tk.Y)
        tv.pack(fill=tk.BOTH, expand=True, padx=20, pady=10)
        
        for c in self.b_cols:
            tv.heading(c, text=c)
            tv.column(c, anchor=tk.W if c in ["荷主名称", "問合せ中分類"] else tk.CENTER)
            
        for _, r in det.iterrows():
            tv.insert("", tk.END, values=(r.get("表示用配送日", r.get("配送日", "")), r.get("デポ名", ""), r.get("ドライバ名", ""), r.get("荷主名称", ""), r.get("問合せ中分類", "")))
            
        tv.bind("<ButtonRelease-1>", lambda e: self.on_popup_tv_click(e, tv, p))

    def open_link(self, idx):
        url = self.links[idx]["url"]
        if url: webbrowser.open(url)
        else: self.edit_link(idx)

    def edit_link(self, idx):
        p = tk.Toplevel(self.root)
        p.title(f"リンク {idx+1} の編集")
        p.geometry("400x200")
        p.configure(bg=CBG)
        p.transient(self.root)
        p.grab_set()
        
        tk.Label(p, text="表示名:", bg=CBG, font=self.fb).pack(pady=5)
        e_name = tk.Entry(p, font=self.fn, width=30)
        e_name.insert(0, self.links[idx]["name"])
        e_name.pack(pady=5)
        
        tk.Label(p, text="URL:", bg=CBG, font=self.fb).pack(pady=5)
        e_url = tk.Entry(p, font=self.fn, width=40)
        e_url.insert(0, self.links[idx]["url"])
        e_url.pack(pady=5)
        
        def _save():
            self.links[idx]["name"] = e_name.get()
            self.links[idx]["url"] = e_url.get()
            self.link_labels[idx].config(text=f"🔗 {self.links[idx]['name']}")
            self.save_db()
            p.destroy()
            
        tk.Button(p, text="保存", bg=CPRI, fg="white", font=self.fb, command=_save).pack(pady=10)

    def pop_settings(self):
        p = tk.Toplevel(self.root)
        p.title("⚙️ 設定")
        p.geometry("500x550")
        p.configure(bg=CBG)
        p.transient(self.root)
        p.grab_set()

        f_al = tk.LabelFrame(p, text=" 🔒 オートロック設定 ", font=self.fb, bg=CBG, fg=CPRI)
        f_al.pack(fill=tk.X, padx=20, pady=20, ipadx=10, ipady=10)
        
        tk.Label(f_al, text="無操作でロック画面に戻る時間:", bg=CBG, font=self.fn).pack(anchor=tk.W, padx=10, pady=(5, 5))
        cb_al = ttk.Combobox(f_al, state="readonly", font=self.fn, values=["1分", "2分", "3分", "4分", "5分", "10分", "15分", "30分", "なし"])
        cb_al.pack(anchor=tk.W, padx=10, pady=5)
        cb_al.set(self.auto_lock_time_str)
        
        def _on_al_change(e):
            self.auto_lock_time_str = cb_al.get()
            self.save_db()
            self.reset_idle_timer()
            
        cb_al.bind("<<ComboboxSelected>>", _on_al_change)
        
        f_db = tk.LabelFrame(p, text=" ⚠ データ管理 ", font=self.fb, bg=CBG, fg="#dc3545")
        f_db.pack(fill=tk.X, padx=20, pady=10, ipadx=10, ipady=10)
        
        lbl_desc = tk.Label(f_db, text="※蓄積した全データを削除し、初期状態に戻します。", bg=CBG, font=self.fs, fg="#6c757d")
        lbl_desc.pack(anchor=tk.W, padx=10, pady=(5, 5))
        
        btn_rst = tk.Button(f_db, text="蓄積データを完全に初期化", bg="#dc3545", fg="white", font=self.fb, command=self.rst_db)
        btn_rst.pack(anchor=tk.W, padx=10, pady=5)

        f_upd = tk.LabelFrame(p, text=" 🔄 アップデート確認 ", font=self.fb, bg=CBG, fg="#28a745")
        f_upd.pack(fill=tk.X, padx=20, pady=10, ipadx=10, ipady=10)
        
        lbl_upd = tk.Label(f_upd, text="最新版の確認とダウンロードページを開きます。", bg=CBG, font=self.fs, fg="#6c757d", justify=tk.LEFT)
        lbl_upd.pack(anchor=tk.W, padx=10, pady=(5, 5))
        
        def _manual_update_check():
            try:
                url = "https://raw.githubusercontent.com/nagashimacrowdworks-pixel/MY-Analyzer/main/version.txt"
                response = requests.get(url, timeout=5)
                if response.status_code == 200:
                    latest_version_str = response.text.strip()
                    try:
                        current_v = float(APP_VERSION)
                        latest_v = float(latest_version_str)
                        if latest_v > current_v:
                            p.destroy()
                            self.prompt_update(latest_version_str)
                        else:
                            messagebox.showinfo("確認", f"現在のバージョン (V{APP_VERSION}) は最新です。", parent=p)
                    except ValueError:
                        if latest_version_str != APP_VERSION:
                            p.destroy()
                            self.prompt_update(latest_version_str)
                        else:
                            messagebox.showinfo("確認", f"現在のバージョン (V{APP_VERSION}) は最新です。", parent=p)
                else:
                    messagebox.showerror("エラー", "バージョン情報の取得に失敗しました。", parent=p)
            except Exception as e:
                messagebox.showerror("エラー", f"通信エラーが発生しました:\n{e}", parent=p)

        btn_check = tk.Button(f_upd, text="最新版をチェック", bg="#0056b3", fg="white", font=self.fb, command=_manual_update_check, width=18)
        btn_check.pack(anchor=tk.W, padx=10, pady=5)

        def _open_github():
            url = "https://github.com/nagashimacrowdworks-pixel/MY-Analyzer/releases/latest"
            try:
                import subprocess
                subprocess.Popen(["cmd", "/c", "start", "firefox", "-private-window", url], shell=True)
            except Exception as e:
                messagebox.showerror("ブラウザ起動エラー", f"Firefoxの起動に失敗しました。Firefoxがインストールされているか確認してください。\n詳細: {e}")

        btn_github = tk.Button(f_upd, text="GitHubを開く", bg="#24292e", fg="white", font=self.fb, command=_open_github, width=18)
        btn_github.pack(anchor=tk.W, padx=10, pady=5)

    def on_t2_itm_selected(self, event=None):
        if getattr(self, 'multi_items_a', []) or getattr(self, 'multi_items_b', []):
            self.multi_items_a = []
            self.multi_items_b = []
        self.request_upd()

    def pop_multi(self):
        p = tk.Toplevel(self.root)
        p.title("比較項目選択 (チェックA / チェックB)")
        p.geometry("600x450")
        p.configure(bg=CBG)
        p.transient(self.root)
        p.grab_set()
        
        tk.Label(p, text="比較する項目をそれぞれのグループで選択してください (複数選択可)", bg=CBG, font=self.fb).pack(pady=5)
        f_main = tk.Frame(p, bg=CBG); f_main.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)
        
        f_a = tk.Frame(f_main, bg=CCARD, bd=1, relief=tk.SOLID); f_a.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5)
        tk.Label(f_a, text="🔴 チェックA (赤棒)", bg=CCARD, font=self.fb, fg="#d62728").pack(pady=5)
        scr_a = ttk.Scrollbar(f_a, orient="vertical")
        lb_a = tk.Listbox(f_a, selectmode=tk.MULTIPLE, yscrollcommand=scr_a.set, font=self.fn, exportselection=False)
        scr_a.config(command=lb_a.yview); scr_a.pack(side=tk.RIGHT, fill=tk.Y); lb_a.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        f_b = tk.Frame(f_main, bg=CCARD, bd=1, relief=tk.SOLID); f_b.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5)
        tk.Label(f_b, text="🔵 チェックB (青棒)", bg=CCARD, font=self.fb, fg="#1f77b4").pack(pady=5)
        scr_b = ttk.Scrollbar(f_b, orient="vertical")
        lb_b = tk.Listbox(f_b, selectmode=tk.MULTIPLE, yscrollcommand=scr_b.set, font=self.fn, exportselection=False)
        scr_b.config(command=lb_b.yview); scr_b.pack(side=tk.RIGHT, fill=tk.Y); lb_b.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        multi_a = getattr(self, 'multi_items_a', [])
        multi_b = getattr(self, 'multi_items_b', [])
        for i, itm in enumerate(self.num_f):
            lb_a.insert(tk.END, itm); lb_b.insert(tk.END, itm)
            if itm in multi_a: lb_a.selection_set(i)
            if itm in multi_b: lb_b.selection_set(i)
                
        def _apply():
            self.multi_items_a = [lb_a.get(i) for i in lb_a.curselection()]
            self.multi_items_b = [lb_b.get(i) for i in lb_b.curselection()]
            if self.multi_items_a or self.multi_items_b:
                if "比較モード(A/B)" not in self.t2_itm['values']:
                    self.t2_itm['values'] = list(self.t2_itm['values']) + ["比較モード(A/B)"]
                self.t2_itm.set("比較モード(A/B)")
            else: self.t2_itm.current(0)
            self.request_upd(); p.destroy()
            
        def _clear():
            lb_a.selection_clear(0, tk.END); lb_b.selection_clear(0, tk.END)
            self.multi_items_a, self.multi_items_b = [], []
            self.t2_itm.current(0); self.request_upd(); p.destroy()
            
        bf = tk.Frame(p, bg=CBG); bf.pack(fill=tk.X, pady=10)
        tk.Button(bf, text="クリア", font=self.fb, command=_clear).pack(side=tk.LEFT, padx=10, expand=True, fill=tk.X)
        tk.Button(bf, text="適用", font=self.fb, bg=CPRI, fg="white", command=_apply).pack(side=tk.RIGHT, padx=10, expand=True, fill=tk.X)

    def on_t2_drv_selected(self, event=None):
        self.multi_drv_list = []
        self.request_upd()

    def pop_multi_drv(self):
        df = self.get_df(ip=True)
        al = sorted(df["ドライバー名"].dropna().astype(str).unique().tolist(), key=self.get_sort_key) if df is not None and "ドライバー名" in df.columns else []
        fd = self.t2_dep.get().strip()
        fl = al if not fd or fd == "すべて" else [d for d in al if str(self.get_driver_depot(d)).strip() == fd]
        
        p = tk.Toplevel(self.root)
        p.title("ドライバー複数選択")
        p.geometry("300x400")
        p.configure(bg=CBG)
        p.transient(self.root)
        p.grab_set()
        
        tk.Label(p, text="比較・表示するドライバーを選択 (複数選択可)", bg=CBG, font=self.fb).pack(pady=5)
        
        f_list = tk.Frame(p, bg=CCARD, bd=1, relief=tk.SOLID)
        f_list.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)
        
        scr = ttk.Scrollbar(f_list, orient="vertical")
        lb = tk.Listbox(f_list, selectmode=tk.MULTIPLE, yscrollcommand=scr.set, font=self.fn, exportselection=False)
        scr.config(command=lb.yview)
        scr.pack(side=tk.RIGHT, fill=tk.Y)
        lb.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        for i, d in enumerate(fl):
            lb.insert(tk.END, d)
            if hasattr(self, 'multi_drv_list') and d in self.multi_drv_list:
                lb.selection_set(i)
                
        def _apply():
            self.multi_drv_list = [lb.get(i) for i in lb.curselection()]
            if self.multi_drv_list:
                val = f"複数({len(self.multi_drv_list)}名)"
                if val not in self.t2_drv['values']:
                    self.t2_drv['values'] = list(self.t2_drv['values']) + [val]
                self.t2_drv.set(val)
            else:
                self.t2_drv.set("全員")
            self.request_upd()
            p.destroy()
            
        def _clear():
            lb.selection_clear(0, tk.END)
            self.multi_drv_list = []
            self.t2_drv.set("全員")
            self.request_upd()
            p.destroy()
            
        bf = tk.Frame(p, bg=CBG)
        bf.pack(fill=tk.X, pady=10)
        tk.Button(bf, text="クリア", font=self.fb, command=_clear).pack(side=tk.LEFT, padx=10, expand=True, fill=tk.X)
        tk.Button(bf, text="適用", font=self.fb, bg=CPRI, fg="white", command=_apply).pack(side=tk.RIGHT, padx=10, expand=True, fill=tk.X)
        
    def show_menu(self, e=None):
        if not self.m_open:
            self.lm.place(x=0, y=50, relheight=0.92); self.lm.lift(); self.m_open = True
            self._menu_check_job = self.root.after(100, self.check_menu_hover)

    def check_menu_hover(self):
        if not self.m_open: return
        x = self.root.winfo_pointerx() - self.root.winfo_rootx()
        y = self.root.winfo_pointery() - self.root.winfo_rooty()
        in_menu = (0 <= x <= 320 and y >= 50)
        in_btn = (0 <= x <= 100 and 0 <= y <= 50)
        if not (in_menu or in_btn):
            self.lm.place_forget(); self.m_open = False
        if self.m_open:
            self._menu_check_job = self.root.after(100, self.check_menu_hover)

    def pop_add_bad(self):
        p = tk.Toplevel(self.root); p.title("🚨 不良配送 手入力追加"); p.geometry("500x350"); p.configure(bg=CBG); p.transient(self.root); p.grab_set()
        pf = tk.Frame(p, bg=CBG, padx=20, pady=20); pf.pack(fill=tk.BOTH, expand=True)

        tk.Label(pf, text="配送日 (YYYY/MM/DD):", bg=CBG, font=self.fb).grid(row=0, column=0, sticky="w", pady=5)
        e_dt = tk.Entry(pf, font=self.fn, bd=1, relief=tk.SOLID, width=20); e_dt.insert(0, datetime.now().strftime("%Y/%m/%d")); e_dt.grid(row=0, column=1, pady=5)

        tk.Label(pf, text="デポ名:", bg=CBG, font=self.fb).grid(row=1, column=0, sticky="w", pady=5)
        e_dp = tk.Entry(pf, font=self.fn, bd=1, relief=tk.SOLID, width=20); e_dp.grid(row=1, column=1, pady=5)

        tk.Label(pf, text="ドライバ名:", bg=CBG, font=self.fb).grid(row=2, column=0, sticky="w", pady=5)
        e_dr = tk.Entry(pf, font=self.fn, bd=1, relief=tk.SOLID, width=20); e_dr.grid(row=2, column=1, pady=5)

        tk.Label(pf, text="荷主名称:", bg=CBG, font=self.fb).grid(row=3, column=0, sticky="w", pady=5)
        e_cl = tk.Entry(pf, font=self.fn, bd=1, relief=tk.SOLID, width=20); e_cl.grid(row=3, column=1, pady=5)

        tk.Label(pf, text="問合せ中分類 (原因):", bg=CBG, font=self.fb).grid(row=4, column=0, sticky="w", pady=5)
        e_rs = tk.Entry(pf, font=self.fn, bd=1, relief=tk.SOLID, width=20); e_rs.grid(row=4, column=1, pady=5)

        def _save():
            v_dt, v_dp, v_dr, v_cl, v_rs = e_dt.get().strip(), e_dp.get().strip(), e_dr.get().strip(), e_cl.get().strip(), e_rs.get().strip()
            if not v_dt or not v_dp or not v_dr or not v_cl or not v_rs: return messagebox.showwarning("警告", "すべての項目を入力してください")
            try: v_dt = pd.to_datetime(v_dt).strftime("%Y/%m/%d")
            except: return messagebox.showwarning("警告", "配送日は正しい形式 (YYYY/MM/DD) で入力してください")
            
            df_new = pd.DataFrame([{"配送日": v_dt, "デポ名": v_dp, "ドライバ名": v_dr, "荷主名称": v_cl, "問合せ中分類": v_rs}])
            for c in self.b_cols:
                if c not in df_new.columns: df_new[c] = ""
            df_new = df_new[self.b_cols].astype(str)
            
            if "manual_added" in self.bad_delivery_data:
                self.bad_delivery_data["manual_added"] = pd.concat([self.bad_delivery_data["manual_added"], df_new], ignore_index=True)
            else: self.bad_delivery_data["manual_added"] = df_new
                
            self.save_db(); self._update_cache(); self.pcb.set("全期間"); self.on_p_change()
            self.request_ref_bad(); self.request_upd()
            messagebox.showinfo("追加完了", "不良データを追加しました。\n全期間・全条件で表示を更新しました。"); p.destroy()

        tk.Button(pf, text="保存", bg=CPRI, fg="white", font=self.fb, command=_save).grid(row=5, column=0, columnspan=2, pady=25, ipadx=30)

    def on_tab_change(self, event=None):
        try:
            idx = self.nb.index("current")
            
            # --- 荷主別詳細タブ(idx=0)では印刷・メールボタンを非表示にする ---
            self.btn_print.pack_forget()
            self.btn_email.pack_forget()
            
            if idx != 0:
                # 元の配置順序（右端から 印刷 → メールの順番）を維持して再表示
                self.btn_print.pack(side=tk.RIGHT, padx=(5, 20), pady=8)
                self.btn_email.pack(side=tk.RIGHT, padx=5, pady=8)
            # -------------------------------------------------------------
            
            # --- タブごとに印刷ボタンの名前を切り替える ---
            if idx == 4:
                self.btn_print.config(text="🖨️ 印刷")
            else:
                self.btn_print.config(text="🖨️ グラフ印刷")
            # ---------------------------------------------
            
            self.ph_frame.pack_forget()
            if idx == 0: self.ph_frame.pack(in_=self.h1_top, side=tk.LEFT, fill=tk.Y)
            elif idx == 1: self.ph_frame.pack(in_=self.h2_top, side=tk.LEFT, fill=tk.Y)
            elif idx == 2: self.ph_frame.pack(in_=self.h3_top, side=tk.LEFT, fill=tk.Y)
            if idx == 3: self.upd_tab4()
            elif idx == 4: pass
            else: self.request_upd()
        except: pass

    def create_login_overlay(self):
        self.login_overlay = tk.Frame(self.root, bg="#87CEEB"); self.login_overlay.place(x=0, y=0, relwidth=1, relheight=1)
        cv = tk.Canvas(self.login_overlay, bg="#87CEEB", highlightthickness=0); cv.place(x=0, y=0, relwidth=1, relheight=1)
        clouds = [(50, 50, 200, 150), (120, 20, 250, 120), (180, 50, 300, 150), (700, 150, 850, 250), (780, 100, 900, 200), (840, 150, 950, 250), (300, 450, 450, 550), (380, 400, 500, 500), (440, 450, 550, 550), (1100, 300, 1250, 400), (1180, 250, 1300, 350), (1240, 300, 1350, 400), (100, 600, 250, 700), (180, 550, 300, 650), (240, 600, 350, 700)]
        for c in clouds: cv.create_oval(c[0], c[1], c[2], c[3], fill="#ffffff", outline="#ffffff")
        self.login_panel = tk.Frame(self.login_overlay, bg="#ffffff", bd=2, relief=tk.RAISED, padx=40, pady=40)
        self.login_panel.place(relx=0.5, rely=0.5, anchor=tk.CENTER)
        self._update_login_panel()

    def _update_login_panel(self):
        for w in self.login_panel.winfo_children(): w.destroy()
        tk.Label(self.login_panel, text="☁ セキュア・ログイン ☁", font=self.ft, bg="#ffffff", fg="#0056b3").pack(pady=(0, 20))
        if not self.my_password:
            tk.Label(self.login_panel, text="初回起動です。\n任意のマイパスワードを設定してください。", font=self.fb, bg="#ffffff").pack(pady=10)
            pw_ent = tk.Entry(self.login_panel, font=self.fn, show="*", width=20, bd=1, relief=tk.SOLID); pw_ent.pack(pady=10)
            def _set_pw(e=None):
                if not pw_ent.get(): return messagebox.showwarning("警告", "パスワードを入力してください")
                self.my_password = pw_ent.get(); self.save_db(); messagebox.showinfo("登録完了", "マイパスワードを登録しました。")
                self._update_login_panel()
                self.reset_idle_timer()
            tk.Button(self.login_panel, text="登録", font=self.fb, bg=CPRI, fg="white", command=_set_pw, width=15).pack(pady=10)
            pw_ent.bind("<Return>", _set_pw); pw_ent.focus_set()
        else:
            tk.Label(self.login_panel, text="マイパスワードを入力してください。", font=self.fb, bg="#ffffff").pack(pady=10)
            pw_ent = tk.Entry(self.login_panel, font=self.fn, show="*", width=20, bd=1, relief=tk.SOLID); pw_ent.pack(pady=10)
            def _login(e=None):
                if pw_ent.get() == self.my_password: 
                    self.login_overlay.place_forget()
                    self.reset_idle_timer()
                else: messagebox.showerror("エラー", "パスワードが違います"); pw_ent.delete(0, tk.END)
            tk.Button(self.login_panel, text="ログイン", font=self.fb, bg=CPRI, fg="white", command=_login, width=15).pack(pady=10)
            pw_ent.bind("<Return>", _login); pw_ent.focus_set()
            def _forgot():
                fp = tk.Toplevel(self.root); fp.title("パスワード初期化"); fp.geometry("400x200"); fp.configure(bg=CBG); fp.transient(self.root); fp.grab_set()
                tk.Label(fp, text="作成者パスワードを入力してください:", bg=CBG, font=self.fb).pack(pady=20)
                apw_ent = tk.Entry(fp, font=self.fn, show="*", bd=1, relief=tk.SOLID); apw_ent.pack(pady=5)
                def _check(e=None):
                    if apw_ent.get() == "qazwsxedc":
                        self.my_password = None; self.save_db(); messagebox.showinfo("初期化", "初期化しました。\n新しいパスワードを設定してください。")
                        fp.destroy(); self._update_login_panel()
                    else: messagebox.showerror("エラー", "作成者パスワードが違います")
                tk.Button(fp, text="確認", font=self.fb, bg="#dc3545", fg="white", command=_check).pack(pady=15)
                apw_ent.bind("<Return>", _check); apw_ent.focus_set()
            tk.Button(self.login_panel, text="パスワードを忘れた場合", font=self.fs, bg="#ffffff", fg="#6c757d", relief=tk.FLAT, command=_forgot).pack(pady=(10, 0))

    def lock_screen(self):
        if self.m_open: self.lm.place_forget(); self.m_open = False
        self.login_overlay.place(x=0, y=0, relwidth=1, relheight=1); self._update_login_panel()
        if getattr(self, 'auto_lock_timer_id', None):
            self.root.after_cancel(self.auto_lock_timer_id)
            self.auto_lock_timer_id = None

    def set_u(self, m):
        self.t2_u = m; self.request_upd()

    def tg_b2(self):
        if self.show_b2: self.b2_tg.config(text="🚨 不良表示", bg="#ffc107", fg="#000000"); self.show_b2 = False
        else: self.b2_tg.config(text="❌ 不良隠す", bg="#dc3545", fg="#ffffff"); self.show_b2 = True
        self.request_upd()

    def clr_bflt(self):
        for cb in [self.bf_dp, self.bf_cl, self.bf_rs]: cb.set("すべて")
        self.bf_dr.delete(0, tk.END); self.request_ref_bad()

    def pop_dep(self):
        p = tk.Toplevel(self.root); p.title("🏢 所属デポマスター管理"); p.geometry("900x650"); p.configure(bg=CBG); p.transient(self.root); p.grab_set()
        pf = tk.Frame(p, bg=CBG, padx=15, pady=15); pf.pack(fill=tk.BOTH, expand=True)
        inf = tk.Frame(pf, bg=CCARD, pady=10, padx=10, bd=1, relief=tk.SOLID); inf.pack(fill=tk.X, pady=(0, 10))
        tk.Label(inf, text="ドライバー:", bg=CCARD, font=self.fb).grid(row=0, column=0, padx=5)
        ed = tk.Entry(inf, font=self.fn, bd=1, relief=tk.SOLID); ed.grid(row=0, column=1, padx=5)
        tk.Label(inf, text="デポ:", bg=CCARD, font=self.fb).grid(row=0, column=2, padx=5)
        ep = tk.Entry(inf, font=self.fn, bd=1, relief=tk.SOLID); ep.grid(row=0, column=3, padx=5)
        btn_frame = tk.Frame(pf, bg=CBG); btn_frame.pack(fill=tk.X, pady=(0, 10))
        lbl_cur = tk.Label(pf, text="表示中: すべて", bg=CBG, font=self.fb, fg=CPRI); lbl_cur.pack(anchor=tk.W, pady=(0, 5))
        t = ttk.Treeview(pf, columns=("drv", "dep"), show="headings"); t.heading("drv", text="ドライバー名"); t.heading("dep", text="所属デポ名"); t.pack(fill=tk.BOTH, expand=True)
        cur_d = ["すべて"]

        def _on_select(event):
            s = t.selection()
            if s:
                item = t.item(s[0], "values")
                ed.delete(0, tk.END); ed.insert(0, item[0])
                ep.delete(0, tk.END)
                if item[1] != "未登録": ep.insert(0, item[1])
        t.bind("<<TreeviewSelect>>", _on_select)

        def _a():
            n, d = ed.get().strip(), self.cln_dep(ep.get())
            if n and d: self.depot_map[n] = d; self.save_db(); _u(); messagebox.showinfo("成功", "保存")
        def _d():
            s = t.selection()
            if s and messagebox.askyesno("削除", "削除しますか？"): del self.depot_map[t.item(s[0], "values")[0]]; self.save_db(); _u()
        
        tk.Button(inf, text="➕ 登録", command=_a, bg=CPRI, fg="white", font=self.fb).grid(row=0, column=4, padx=5)
        tk.Button(inf, text="❌ 削除", command=_d, bg="#dc3545", fg="white", font=self.fb).grid(row=0, column=5, padx=5)

        def _show(d):
            cur_d[0] = d; lbl_cur.config(text=f"表示中: {d}"); t.delete(*t.get_children())
            for k, v in sorted(self.depot_map.items()):
                if d == "すべて" or v == d: t.insert("", "end", values=(k, v))

        def _u():
            for w in btn_frame.winfo_children(): w.destroy()
            dps = ["すべて"] + sorted(list(set(self.depot_map.values())))
            for i, d in enumerate(dps):
                tk.Button(btn_frame, text=d, font=self.fs, bg=CACC if d!="すべて" else "#6c757d", fg="white", command=lambda dx=d: _show(dx)).grid(row=i//8, column=i%8, padx=2, pady=2, sticky="ew")
            _show(cur_d[0]); self.request_upd()
        _u()

    def pop_cal(self):
        p = tk.Toplevel(self.root); p.title("📅 読込状況詳細カレンダー"); p.geometry("850x650"); p.configure(bg=CBG); p.transient(self.root)
        cf = tk.Frame(p, bg=CCARD, padx=15, pady=15); cf.pack(fill=tk.BOTH, expand=True)
        hc = tk.Frame(cf, bg=CCARD); hc.pack(fill=tk.X, pady=(0, 10))
        st = {"y": datetime.now().year, "m": datetime.now().month}
        
        yc = ttk.Combobox(hc, state="readonly", values=[f"{y}年" for y in range(2024, 2031)], font=self.fb, width=8); yc.pack(side=tk.LEFT, padx=5); yc.set(f"{st['y']}年")
        tk.Label(hc, text="デポ:", bg=CCARD, font=self.fb).pack(side=tk.LEFT, padx=(30, 5))
        dc = ttk.Combobox(hc, state="readonly", values=["すべて"] + sorted(list(set(self.depot_map.values()))), font=self.fn, width=14); dc.set("すべて"); dc.pack(side=tk.LEFT, padx=5)
        mc_frame = tk.Frame(cf, bg=CCARD); mc_frame.pack(fill=tk.X, pady=(0, 10))
        bd = tk.Frame(cf, bg=CBG); bd.pack(fill=tk.BOTH, expand=True)

        def _draw_cal(y, m, cd):
            for w in bd.winfo_children(): w.destroy()
            ld = set()
            if self.cached_df is not None and not self.cached_df.empty and "日付" in self.cached_df.columns:
                if cd == "すべて": ld.update(self.cached_df["日付"].unique().tolist())
                else:
                    s = self.cached_df[self.cached_df["所属デポ"] == cd]
                    if not s.empty: ld.update(s["日付"].unique().tolist())
                    
            f = tk.LabelFrame(bd, text=f" 📅 {y}年 {m}月 ", font=self.ft, bg=CCARD, fg=CPRI); f.pack(fill=tk.BOTH, expand=True, padx=5)
            g = tk.Frame(f, bg="#cfd8dc"); g.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
            for idx, day in enumerate(W_JA): tk.Label(g, text=day, font=self.fb, bg=CPRI if day not in ["土","日"] else (CSAT if day=="土" else CSUN), fg="white", pady=4).grid(row=0, column=idx, sticky="nsew", padx=1, pady=1)
            for r_idx, week in enumerate(calendar.Calendar(firstweekday=6).monthdayscalendar(y, m)):
                for c_idx, day in enumerate(week):
                    if day == 0: tk.Label(g, text="", bg=CBG).grid(row=r_idx+1, column=c_idx, sticky="nsew", padx=1, pady=1)
                    else:
                        ds = f"{y}/{m:02d}/{day:02d}"; isl = ds in ld
                        tk.Button(g, text=f"{day}\n(データ有)" if isl else f"{day}", font=self.fn, bg=CHL if isl else CCARD, fg=CSUN if c_idx==0 else (CSAT if c_idx==6 else CTXT), relief=tk.FLAT, command=lambda d=ds: _o(d, cd)).grid(row=r_idx+1, column=c_idx, sticky="nsew", padx=1, pady=1)
            for i in range(7): g.columnconfigure(i, weight=1)
            for i in range(len(calendar.Calendar(firstweekday=6).monthdayscalendar(y, m))+1): g.rowconfigure(i, weight=1)

        def _set_m(m): st["m"] = m; _draw_cal(st["y"], st["m"], dc.get())
        for m in range(1, 13): tk.Button(mc_frame, text=f"{m}月", font=self.fb, bg=CPRI, fg="white", command=lambda mx=m: _set_m(mx)).pack(side=tk.LEFT, fill=tk.X, expand=True, padx=2)

        yc.bind("<<ComboboxSelected>>", lambda e: st.update({"y": int(yc.get().replace("年",""))}) or _draw_cal(st["y"], st["m"], dc.get()))
        dc.bind("<<ComboboxSelected>>", lambda e: _draw_cal(st["y"], st["m"], dc.get()))
        
        def _o(ds, cd):
            dl = []
            if self.cached_df is not None and not self.cached_df.empty and "日付" in self.cached_df.columns:
                s = self.cached_df[self.cached_df["日付"] == ds]
                if cd != "すべて": s = s[s["所属デポ"] == cd]
                if not s.empty: dl.extend(s["ドライバー名"].unique().tolist())
            if not dl: return messagebox.showinfo("確認", "データなし")
            dp = tk.Toplevel(p); dp.title("管理"); dp.geometry("400x350"); dp.configure(bg=CBG); dp.transient(p); dp.grab_set()
            tk.Label(dp, text=f"📅 {ds} ({cd})", font=self.ft, bg=CBG, fg=CPRI).pack(pady=10)
            sc = tk.Listbox(dp, font=self.fn); sc.pack(fill=tk.BOTH, expand=True, padx=20, pady=5)
            for d in sorted(list(set(dl)), key=self.get_sort_key): sc.insert(tk.END, d)

            def _dt():
                if messagebox.askyesno("警告", "削除しますか？"):
                    for k, df in list(self.all_data.items()):
                        if isinstance(df, pd.DataFrame) and not df.empty and "日付" in df.columns:
                            self.all_data[k] = df[df["日付"] != ds] if cd == "すべて" else df[~((df["日付"] == ds) & (df["所属デポ"] == cd))]
                    self.save_db(); self._update_cache(); self.request_upd(); dp.destroy(); _draw_cal(st["y"], st["m"], dc.get()); messagebox.showinfo("完了", "削除完了")
            tk.Button(dp, text="🗑️ 削除", command=_dt, bg="#dc3545", fg="white", font=self.fb).pack(side=tk.BOTTOM, fill=tk.X, padx=20, pady=15)
        _draw_cal(st["y"], st["m"], dc.get())

    def on_p_change(self, e=None):
        p = self.pcb.get()
        self.lbl_start.pack_forget(); self.start_p_frame.pack_forget(); self.lbl_end.pack_forget(); self.end_p_frame.pack_forget()
        if p != "全期間":
            self.lbl_start.pack(side=tk.LEFT, padx=2); self.start_p_frame.pack(side=tk.LEFT, padx=2)
            if p == "年間指定 (12ヶ月)": self.sm.pack_forget(); self.sd.pack_forget(); self.ed.pack_forget()
            elif p == "月間指定 (1ヶ月)": self.sm.pack(side=tk.LEFT, padx=1); self.sd.pack_forget(); self.ed.pack_forget()
            else: self.sm.pack(side=tk.LEFT, padx=1); self.sd.pack(side=tk.LEFT, padx=1)
            if p == "任意の期間指定":
                self.lbl_end.pack(side=tk.LEFT, padx=2); self.end_p_frame.pack(side=tk.LEFT, padx=2)
                self.em.pack(side=tk.LEFT, padx=1); self.ed.pack(side=tk.LEFT, padx=1)
        self.upd_pcb_v(); self.request_upd()

    def on_t2_dep(self, e=None):
        df = self.get_df(ip=True)
        al = sorted(df["ドライバー名"].dropna().astype(str).unique().tolist(), key=self.get_sort_key) if df is not None and "ドライバー名" in df.columns else []
        fd = self.t2_dep.get().strip()
        fl = ["全員"] + (al if not fd or fd == "すべて" else [d for d in al if str(self.get_driver_depot(d)).strip() == fd])
        c = self.t2_drv.get(); self.t2_drv["values"] = fl
        self.t2_drv.set(c if c in fl else "全員")
        if e is not None: self.request_upd()

    def pcd(self, t="start"):
        y = self.sy.get().replace("年", "") if t == "start" else self.ey.get().replace("年", "")
        m = self.sm.get().replace("月", "") if t == "start" else self.em.get().replace("月", "")
        d = self.sd.get().replace("日", "") if t == "start" else self.ed.get().replace("日", "")
        if t == "start":
            if not y: return None
            return f"{y}/{m if m else '01'}/{d if d else '01'}"
        else:
            if not y or not m or not d: return None
            return f"{y}/{m}/{d}"

    def get_df(self, ip=False):
        if self.cached_df is None: return None
        df = self.cached_df
        if ip or df.empty or "_dt" not in df.columns: return df
        p, sd, ed = self.pcb.get(), self.pcd("start"), self.pcd("end")
        try:
            if p == "日付指定 (1日)" and sd: df = df[df["_dt"].dt.date == pd.to_datetime(sd).date()]
            elif p == "週間指定 (7日間)" and sd: sdt = pd.to_datetime(sd); df = df[(df["_dt"] >= sdt) & (df["_dt"] <= sdt + pd.Timedelta(days=6))]
            elif p == "月間指定 (1ヶ月)" and sd: sdt = pd.to_datetime(sd); df = df[(df["_dt"].dt.year == sdt.year) & (df["_dt"].dt.month == sdt.month)]
            elif p == "年間指定 (12ヶ月)" and sd: sdt = pd.to_datetime(sd); df = df[df["_dt"].dt.year == sdt.year]
            elif p == "任意の期間指定" and sd and ed: df = df[(df["_dt"] >= pd.to_datetime(sd)) & (df["_dt"] <= pd.to_datetime(ed))]
        except: pass
        return df

    def get_bad_df(self):
        if self.bad_cached_df is None or self.bad_cached_df.empty: return None
        df = self.bad_cached_df.copy()
        if "_dt" not in df.columns: return df
        p, sd, ed = self.pcb.get(), self.pcd("start"), self.pcd("end")
        try:
            if p == "日付指定 (1日)" and sd: df = df[df["_dt"].dt.date == pd.to_datetime(sd).date()]
            elif p == "週間指定 (7日間)" and sd: sdt = pd.to_datetime(sd); df = df[(df["_dt"] >= sdt) & (df["_dt"] <= sdt + pd.Timedelta(days=6))]
            elif p == "月間指定 (1ヶ月)" and sd: sdt = pd.to_datetime(sd); df = df[(df["_dt"].dt.year == sdt.year) & (df["_dt"].dt.month == sdt.month)]
            elif p == "年間指定 (12ヶ月)" and sd: sdt = pd.to_datetime(sd); df = df[df["_dt"].dt.year == sdt.year]
            elif p == "任意の期間指定" and sd and ed: df = df[(df["_dt"] >= pd.to_datetime(sd)) & (df["_dt"] <= pd.to_datetime(ed))]
        except: pass
        return df

    def setup_initial_comboboxes(self):
        base_df = self.get_df(ip=True)
        if base_df is not None and not base_df.empty:
            depots_in_df = base_df["所属デポ"].dropna().astype(str).unique().tolist() if "所属デポ" in base_df.columns else []
            ud = sorted(list(set(depots_in_df + list(self.depot_map.values()))))
            if "未登録" in ud: ud.remove("未登録")
            d_opts = ["すべて", "未登録"] + ud
            self.t1_cb["values"] = d_opts
            self.t2_dep["values"] = d_opts
            if "ドライバー名" in base_df.columns:
                al = sorted(base_df["ドライバー名"].dropna().astype(str).unique().tolist(), key=self.get_sort_key)
                self.t2_drv["values"] = ["全員"] + al

    def upd(self):
        try:
            current_tab = self.nb.index("current")
            df = self.get_df()
            if current_tab == 0: self.upd_tab1(df)
            elif current_tab == 1: self.upd_tab2(df)
            elif current_tab == 2: self.ref_bad()
        except Exception as ex: print(f"Upd err: {ex}")

    def upd_tab1(self, df):
        self.tv1.delete(*self.tv1.get_children())
        if df is None or df.empty: return
        ar = {f: "sum" for f in self.num_f}; ar.update({f: "first" for f in self.txt_f})
        sm = df.groupby("ドライバー名").agg(ar).reset_index()
        sm["所属デポ"] = sm["ドライバー名"].apply(self.get_driver_depot)
        for num_col in self.num_f:
            if num_col in sm.columns: sm[num_col] = sm[num_col].fillna(0)
        sort_val = self.t1_sort.get()
        sm = sm.sort_values(by="全体個数", ascending=(sort_val == "実績(少ない順)"))
        t1f = self.t1_cb.get()

        rows_to_insert = []
        for _, r in sm.iterrows():
            rd = r["所属デポ"]
            if t1f and t1f != "すべて":
                if t1f == "未登録" and rd != "未登録": continue
                if t1f != "未登録" and rd != t1f: continue
            v = [r["ドライバー名"], rd]
            for f in self.v_cols[2:]:
                vl = r.get(f, 0.0 if f in self.num_f else "")
                v.append(f"{int(vl)}円" if f in ["チャーター①", "チャーター②", "チャーター③"] else (f"{int(vl)}" if f in self.num_f else str(vl)))
            rows_to_insert.append(v)
        for row in rows_to_insert: self.tv1.insert("", tk.END, values=row)
        
    def upd_tab2(self, df):
        try:
            self.tv2.delete(*self.tv2.get_children()); self.clr_p(self.a2, self.cv2, "データなし", show_img_links=True)
            if df is None or df.empty: return
            df_calc = df.copy()
            df_calc["所属デポ"] = df_calc["ドライバー名"].apply(lambda x: str(self.get_driver_depot(x)).strip())
            td, tdp, p = self.t2_drv.get(), self.t2_dep.get().strip(), self.pcb.get()
            sd_val, ed_val = self.pcd("start"), self.pcd("end")
            
            multi_a, multi_b = getattr(self, 'multi_items_a', []), getattr(self, 'multi_items_b', [])
            is_compare = bool(multi_a) or bool(multi_b)
            valid_multi_a = [c for c in multi_a if c in df_calc.columns]
            valid_multi_b = [c for c in multi_b if c in df_calc.columns]
            
            raw_itm = self.t2_itm.get()
            if not is_compare and (not raw_itm or raw_itm not in df_calc.columns):
                if "全体個数" in df_calc.columns:
                    if "全体個数" not in self.t2_itm['values']: self.t2_itm['values'] = list(self.t2_itm['values']) + ["全体個数"]
                    self.t2_itm.set("全体個数"); raw_itm = "全体個数"
                else: return
                    
            target_items = list(set(valid_multi_a + valid_multi_b)) if is_compare else [raw_itm]
            if not target_items or target_items[0] == "": return
            if not is_compare and target_items[0] not in df_calc.columns: return
                
            u_str = "個/円" if is_compare else ("円" if target_items[0] in ["チャーター①", "チャーター②", "チャーター③"] else "個")
            
            if td and "ドライバー名" in df_calc.columns:
                if td == "全員":
                    sd = df_calc[df_calc["所属デポ"] == tdp].copy() if tdp and tdp != "すべて" else df_calc.copy()
                elif td.startswith("複数(") and hasattr(self, 'multi_drv_list') and self.multi_drv_list:
                    sd = df_calc[df_calc["ドライバー名"].isin(self.multi_drv_list)].copy()
                else: sd = df_calc[df_calc["ドライバー名"] == td].copy()
                    
                if not sd.empty:
                    agg_dict = {itm: "sum" for itm in target_items}
                    if self.t2_u == "month":
                        sd["k"] = sd["_dt"].dt.strftime("%Y/%m")
                        ds = sd.groupby("k").agg(agg_dict).reset_index().rename(columns={"k": "日付"})
                        start_yr = sd["_dt"].min().year if not sd["_dt"].dropna().empty else datetime.now().year
                        end_yr = sd["_dt"].max().year if not sd["_dt"].dropna().empty else datetime.now().year
                        all_months = pd.date_range(start=f"{start_yr}-01-01", end=f"{end_yr}-12-31", freq='MS').strftime("%Y/%m")
                        ds = pd.merge(pd.DataFrame({"日付": all_months}), ds, on="日付", how="left").fillna(0); ds["w"] = -1
                        ds = ds.sort_values(by="日付")
                        
                        if is_compare:
                            ds["v_a"] = ds[valid_multi_a].sum(axis=1) if valid_multi_a else 0
                            ds["v_b"] = ds[valid_multi_b].sum(axis=1) if valid_multi_b else 0
                            wa_a = ds[ds["v_a"] > 0]["v_a"].mean() if not ds[ds["v_a"] > 0].empty else 0
                            wa_b = ds[ds["v_b"] > 0]["v_b"].mean() if not ds[ds["v_b"] > 0].empty else 0
                            wa, tfa = (wa_a, wa_b), (0, 0)
                        else:
                            ds["v"] = ds[target_items[0]]
                            wa = ds[ds["v"] > 0]["v"].mean() if not ds[ds["v"] > 0].empty else 0
                            tfa = 0
                        
                        sd_tfa = sd[sd["_dt"].dt.dayofweek.isin([1,2,3,4])]
                        if not sd_tfa.empty:
                            sd_tfa["k"] = sd_tfa["_dt"].dt.strftime("%Y/%m")
                            tfa_grp = sd_tfa.groupby("k").agg(agg_dict)
                            if is_compare:
                                v_a_tfa = tfa_grp[valid_multi_a].sum(axis=1) if valid_multi_a else pd.Series(0, index=tfa_grp.index)
                                v_b_tfa = tfa_grp[valid_multi_b].sum(axis=1) if valid_multi_b else pd.Series(0, index=tfa_grp.index)
                                tfa_a = v_a_tfa[v_a_tfa > 0].mean() if not v_a_tfa[v_a_tfa > 0].empty else 0
                                tfa_b = v_b_tfa[v_b_tfa > 0].mean() if not v_b_tfa[v_b_tfa > 0].empty else 0
                                tfa = (tfa_a, tfa_b)
                            else:
                                tfa_grp["v"] = tfa_grp[target_items[0]]
                                tfa = tfa_grp[tfa_grp["v"] > 0]["v"].mean() if not tfa_grp[tfa_grp["v"] > 0].empty else 0
                    else:
                        ds = sd.groupby(["日付", "_dt"]).agg(agg_dict).reset_index()
                        if sd_val and p in ["月間指定 (1ヶ月)", "週間指定 (7日間)", "任意の期間指定", "年間指定 (12ヶ月)"]:
                            try:
                                sdt = pd.to_datetime(sd_val)
                                if p == "月間指定 (1ヶ月)": 
                                    sdt = sdt.replace(day=1)
                                    edt = sdt + pd.offsets.MonthEnd(0)
                                elif p == "週間指定 (7日間)": edt = sdt + pd.Timedelta(days=6)
                                elif p == "年間指定 (12ヶ月)": edt = sdt.replace(month=12, day=31); sdt = sdt.replace(month=1, day=1)
                                else: edt = pd.to_datetime(ed_val)
                                all_days = pd.date_range(start=sdt, end=edt).strftime("%Y/%m/%d")
                                ds = pd.merge(pd.DataFrame({"日付": all_days}), ds, on="日付", how="left").fillna(0)
                            except: pass
                        ds["_dt"] = pd.to_datetime(ds["日付"])
                        ds["w"] = ds["_dt"].dt.dayofweek
                        
                        if is_compare:
                            ds["v_a"] = ds[valid_multi_a].sum(axis=1) if valid_multi_a else 0
                            ds["v_b"] = ds[valid_multi_b].sum(axis=1) if valid_multi_b else 0
                            wa_a = ds[ds["v_a"] > 0]["v_a"].mean() if not ds[ds["v_a"] > 0].empty else 0
                            wa_b = ds[ds["v_b"] > 0]["v_b"].mean() if not ds[ds["v_b"] > 0].empty else 0
                            ds_tfa_a = ds[(ds["w"].isin([1, 2, 3, 4])) & (ds["v_a"] > 0)]
                            ds_tfa_b = ds[(ds["w"].isin([1, 2, 3, 4])) & (ds["v_b"] > 0)]
                            tfa_a = ds_tfa_a["v_a"].mean() if not ds_tfa_a.empty else 0
                            tfa_b = ds_tfa_b["v_b"].mean() if not ds_tfa_b.empty else 0
                            wa, tfa = (wa_a, wa_b), (tfa_a, tfa_b)
                        else:
                            ds["v"] = ds[target_items[0]]
                            ds_valid = ds[ds["v"] > 0]
                            wa = ds_valid["v"].mean() if not ds_valid.empty else 0
                            ds_tfa = ds_valid[ds_valid["w"].isin([1, 2, 3, 4])]
                            tfa = ds_tfa["v"].mean() if not ds_tfa.empty else 0
                    
                    if is_compare: self.l2_avg.config(text=f"A平均: {wa[0]:.1f}{u_str} / B平均: {wa[1]:.1f}{u_str}")
                    else: self.l2_avg.config(text=f"平均(0除外): {wa:.1f}{u_str} | 火～金(0除外): {tfa:.1f}{u_str}")
                    
                    rows_to_insert = []
                    for _, r in ds.iterrows():
                        if is_compare:
                            v_str, vw_str, vtf_str = f"A:{int(r['v_a'])} B:{int(r['v_b'])}", "--", "--"
                        else:
                            v_str = f"{int(r['v'])}"
                            vw_str = f"{int(r['v']-wa):+d}" if r['v']>0 else "--"
                            vtf_str = f"{int(r['v']-tfa):+d}" if r['v']>0 else "--"
                        rows_to_insert.append((r["日付"], W_JA[(int(r["w"]) + 1) % 7] if r["w"] >= 0 else "--", v_str, vw_str, vtf_str))

                    for row in rows_to_insert: self.tv2.insert("", tk.END, values=row)
                    
                    if td == "全員":
                        tgt_title = f"{tdp}デポ 全員" if tdp and tdp != "すべて" else "全員"
                    elif td.startswith("複数(") and hasattr(self, 'multi_drv_list') and self.multi_drv_list:
                        tgt_title = f"{tdp}デポ 複数({len(self.multi_drv_list)}名)" if tdp and tdp != "すべて" else f"複数({len(self.multi_drv_list)}名)"
                    else:
                        tgt_title = f"{td}"
                        
                    tf_title = "比較モード(チェックA/B)" if is_compare else target_items[0]
                    title_str = f"📊 {tgt_title} : {tf_title} ({'月別' if self.t2_u=='month' else '日別'})"
                    
                    self.drw(self.a2, self.cv2, ds, wa, tfa, title_str, u_str, tgt=td, um=self.t2_u, is_compare=is_compare, multi_a=valid_multi_a, multi_b=valid_multi_b)
        except Exception as e: print(f"Error in upd_tab2: {e}")

    def ref_bad(self):
        self.tv4.delete(*self.tv4.get_children()); self.clr_p(self.a4, self.cv4, "データなし")
        bdf = self.get_bad_df()
        if bdf is None or bdf.empty: return
        df = bdf.copy()
        
        dps = ["すべて"] + sorted(list(set(self.cln_dep(d) for d in df["デポ名"].dropna().unique())))
        cls = ["すべて"] + sorted(list(set(df["荷主名称"].dropna().unique())))
        rs = ["すべて"] + sorted(list(set(df["問合せ中分類"].dropna().unique())))
        for cb, vs in [(self.bf_dp, dps), (self.bf_cl, cls), (self.bf_rs, rs)]:
            c = cb.get(); cb["values"] = vs; cb.set(c if c in vs else "すべて")
        
        df["デポ名"] = df["デポ名"].apply(self.cln_dep)
        fdp, fcl, frs, fdr = self.bf_dp.get(), self.bf_cl.get(), self.bf_rs.get(), self.bf_dr.get().strip()
        if fdp and fdp != "すべて": df = df[df["デポ名"] == fdp]
        if fcl and fcl != "すべて": df = df[df["荷主名称"] == fcl]
        if frs and frs != "すべて": df = df[df["問合せ中分類"] == frs]
        if fdr: df = df[df["ドライバ名"].str.contains(fdr, na=False)]
        
        if "_dt" in df.columns: df["_dt_sort"] = df["_dt"]
        else:
            ext_dt = df["配送日"].astype(str).str.extract(r'(\d{4}[-/]\d{1,2}[-/]\d{1,2})')[0]
            df["_dt_sort"] = pd.to_datetime(ext_dt, errors='coerce').fillna(pd.to_datetime(df["配送日"], errors='coerce'))
        
        sbd = df.sort_values(by="_dt_sort", ascending=False, na_position='last')
        sbd["表示用配送日"] = sbd["_dt_sort"].dt.strftime("%Y/%m/%d").fillna(sbd["配送日"])
        
        rows_to_insert = []
        for _, r in sbd.iterrows():
            rows_to_insert.append((r.get("表示用配送日",""), r.get("デポ名",""), r.get("ドライバ名",""), r.get("荷主名称",""), r.get("問合せ中分類","")))

        if not rows_to_insert: return
        for row in rows_to_insert: self.tv4.insert("", tk.END, values=row)
        if self.IsTesting(): return
        
        graph_df = sbd.dropna(subset=["_dt_sort"]).copy()
        graph_df = graph_df.sort_values(by="_dt_sort", ascending=True)
        graph_df["配送日"] = graph_df["_dt_sort"].dt.strftime("%Y/%m/%d")

        p, sd_val, ed_val = self.pcb.get(), self.pcd("start"), self.pcd("end")
        
        if p == "年間指定 (12ヶ月)":
            graph_df["配送月"] = graph_df["_dt_sort"].dt.strftime("%Y/%m")
            ct = graph_df.groupby("配送月").size().reset_index(name="cnt")
            if sd_val:
                try:
                    sdt = pd.to_datetime(sd_val).replace(month=1, day=1)
                    all_months = pd.date_range(start=sdt, end=sdt.replace(month=12, day=31), freq='MS').strftime("%Y/%m")
                    ct = pd.merge(pd.DataFrame({"配送月": all_months}), ct, on="配送月", how="left").fillna({"cnt": 0})
                except: pass
            ct = ct.rename(columns={"配送月": "配送日"})
        else:
            ct = graph_df.groupby("配送日").size().reset_index(name="cnt")
            if sd_val and p in ["月間指定 (1ヶ月)", "週間指定 (7日間)", "任意の期間指定"]:
                try:
                    sdt = pd.to_datetime(sd_val)
                    if p == "月間指定 (1ヶ月)": edt = sdt.replace(day=1) + pd.offsets.MonthEnd(0); sdt = sdt.replace(day=1)
                    elif p == "週間指定 (7日間)": edt = sdt + pd.Timedelta(days=6)
                    else: edt = pd.to_datetime(ed_val)
                    all_days = pd.date_range(start=sdt, end=edt).strftime("%Y/%m/%d")
                    ct = pd.merge(pd.DataFrame({"配送日": all_days}), ct, on="配送日", how="left").fillna({"cnt": 0})
                except: pass
            else:
                if len(ct) > 31: ct = ct.tail(31)
        
        ct = ct.sort_values("配送日")
        self.a4.axis('on'); self.a4.set_xticks(range(len(ct)))
        brs = self.a4.bar(range(len(ct)), ct["cnt"], color="#e74c3c", edgecolor=CTXT, linewidth=0.5)
        self.a4.set_title(f"📊 📅日付別 不良発生推移 ({fdp})", color=CPRI, fontname="MS Gothic", weight='bold', fontsize=self.f_size-1)
        self.a4.set_xticklabels(ct["配送日"].tolist(), rotation=45 if len(ct)<=31 else 90, ha="center"); self.a4.tick_params(labelsize=self.f_size-3)
        for b in brs: 
            h = b.get_height()
            if h > 0: self.a4.annotate(f'{int(h)}', xy=(b.get_x() + b.get_width() / 2, h), xytext=(0, 2), textcoords="offset points", ha='center', va='bottom', fontsize=self.f_size - 4, weight='bold')
        self.f4.tight_layout(); self.cv4.draw()

        info_dict = {}
        for i, (_, row) in enumerate(ct.iterrows()):
            if row["cnt"] > 0:
                dt = row["配送日"]
                det = graph_df[graph_df["配送月"] == dt] if len(dt) == 7 and "配送月" in graph_df.columns else graph_df[graph_df["配送日"].str.startswith(dt)] if len(dt) == 7 else graph_df[graph_df["配送日"] == dt]
                if not det.empty:
                    vc = det.groupby(["問合せ中分類", "ドライバ名"]).size().reset_index(name="c").sort_values("c", ascending=False)
                    txt_lines = [f"{vr['問合せ中分類']} - {self.get_driver_depot(vr['ドライバ名'])} {vr['ドライバ名'][:4]}: {vr['c']}件" for _, vr in vc.iterrows()]
                    info_dict[i] = f"【{dt}】\n" + "\n".join(txt_lines)

        self.add_hover(self.a4, self.cv4, brs, info_dict)
        self.add_bad_click_event(self.a4, self.cv4, brs, ct, graph_df)

    def add_bad_click_event(self, ax, cv, bars, ct, graph_df):
        if hasattr(self, 'bad_click_cid'): cv.mpl_disconnect(self.bad_click_cid)
        def on_click(event):
            if event.inaxes == ax:
                for i, bar in enumerate(bars):
                    if bar.contains(event)[0]:
                        self.tooltip.hide()
                        dt = ct.iloc[i]["配送日"]
                        self.pop_bad_list_for_date(dt, graph_df)
                        break
        self.bad_click_cid = cv.mpl_connect("button_press_event", on_click)
        
    def drw(self, ax, cv, sdf, wa, tfa, tt, u, tgt=None, um=None, is_compare=False, multi_a=None, multi_b=None):
        if self.IsTesting(): return
        ax.clear(); ax.axis('on')
        sd = [str(d) if len(str(d)) <= 7 else str(d)[-5:] for d in sdf["日付"].tolist()]
        xl_str = sdf["日付"].tolist()
        x_pos = range(len(sd))
        
        if is_compare:
            w = 0.35
            x_a = [x - w/2 for x in x_pos]
            x_b = [x + w/2 for x in x_pos]
            
            if multi_a:
                bars_a = ax.bar(x_a, sdf["v_a"], width=w, label="A (赤棒)", color="#d62728", edgecolor=CTXT, linewidth=0.5)
                for b in bars_a:
                    if b.get_height() > 0: ax.annotate(f'{int(b.get_height())}', xy=(b.get_x() + b.get_width() / 2, b.get_height()), xytext=(0, 2), textcoords="offset points", ha='center', va='bottom', fontsize=self.f_size - 5, weight='bold')
            if multi_b:
                bars_b = ax.bar(x_b, sdf["v_b"], width=w, label="B (青棒)", color="#1f77b4", edgecolor=CTXT, linewidth=0.5)
                for b in bars_b:
                    if b.get_height() > 0: ax.annotate(f'{int(b.get_height())}', xy=(b.get_x() + b.get_width() / 2, b.get_height()), xytext=(0, 2), textcoords="offset points", ha='center', va='bottom', fontsize=self.f_size - 5, weight='bold')
            
            wa_a, wa_b = wa
            tfa_a, tfa_b = tfa
            if wa_a > 0: ax.axhline(y=wa_a, color="#d62728", linestyle="-", linewidth=2, alpha=0.6, label=f"A全日平均 ({wa_a:.1f})")
            if wa_b > 0: ax.axhline(y=wa_b, color="#1f77b4", linestyle="-", linewidth=2, alpha=0.6, label=f"B全日平均 ({wa_b:.1f})")
            if tfa_a > 0: ax.axhline(y=tfa_a, color="#d62728", linestyle=":", linewidth=2, label=f"A火~金 ({tfa_a:.1f})")
            if tfa_b > 0: ax.axhline(y=tfa_b, color="#1f77b4", linestyle=":", linewidth=2, label=f"B火~金 ({tfa_b:.1f})")
            ax.legend(loc="upper left", bbox_to_anchor=(1.01, 1), fontsize=self.f_size - 4, borderaxespad=0.)
        else:
            brs_main = ax.bar(x_pos, sdf["v"], width=0.8, color="#3498db", edgecolor=CTXT, linewidth=0.5)
            for b in brs_main:
                if b.get_height() > 0: ax.annotate(f'{int(b.get_height())}', xy=(b.get_x() + b.get_width() / 2, b.get_height()), xytext=(0, 2), textcoords="offset points", ha='center', va='bottom', fontsize=self.f_size - 4, weight='bold')
            ax.axhline(y=wa, color="#e67e22", linestyle="--", linewidth=1.5, label=f"平均 ({wa:.1f})")
            if tfa > 0: ax.axhline(y=tfa, color="#c53030", linestyle="-.", linewidth=1.5, label=f"火～金 ({tfa:.1f})")
            ax.legend(loc="upper left", bbox_to_anchor=(1.01, 1), fontsize=self.f_size - 4, borderaxespad=0.)
        
        ax.set_title(tt, color=CPRI, fontname="MS Gothic", weight='bold', pad=8)
        ax.set_xticks(range(len(sd))); ax.set_xticklabels(sd, rotation=90, ha="center"); ax.tick_params(labelsize=self.f_size-3)

        info_dict = {}
        red_bars = []

        if self.show_b2 and tgt is not None:
            bdf = self.get_bad_df()
            df_bad = bdf.copy() if bdf is not None else pd.DataFrame()
            if not df_bad.empty:
                df_bad["デポ名"] = df_bad["デポ名"].apply(self.cln_dep)
                if tgt == "全員":
                    tdp = self.t2_dep.get().strip()
                    sub = df_bad[df_bad["デポ名"] == tdp] if tdp and tdp != "すべて" else df_bad.copy()
                else: sub = df_bad[df_bad["ドライバ名"] == tgt]
                
                if um == "month": sub["dk"] = pd.to_datetime(sub["配送日"], errors='coerce').dt.strftime("%Y/%m")
                else: sub["dk"] = pd.to_datetime(sub["配送日"], errors='coerce').dt.strftime("%Y/%m/%d")
                    
                xl_str_adj = [str(x).replace("-", "/") for x in xl_str]
                sub = sub[sub["dk"].isin(xl_str_adj)]
                ct = sub["dk"].value_counts().to_dict()
                
                for i, (d_str, v_val) in enumerate(zip(xl_str_adj, sdf["v_a"] if is_compare else sdf["v"])):
                    bad_count = ct.get(d_str, 0)
                    if bad_count > 0:
                        draw_h = max(v_val, bad_count) if max(v_val, bad_count) > 0 else bad_count
                        bar_pos = i + 0.2 if not is_compare else i
                        bar_w = 0.4 if not is_compare else 0.8
                        r_bar = ax.bar(bar_pos, draw_h, width=bar_w, color="#cf3545", edgecolor="#c53030", linewidth=1.5, fill=False, hatch='//', zorder=4)
                        
                        det = sub[sub["dk"] == d_str]
                        vc = det.groupby(["問合せ中分類", "ドライバ名"]).size().reset_index(name="c").sort_values("c", ascending=False)
                        txt_lines = [f"🚨 不良件数: {bad_count}件"]
                        for _, vr in vc.iterrows():
                            txt_lines.append(f"{vr['問合せ中分類']} - {self.get_driver_depot(vr['ドライバ名'])} {vr['ドライバ名'][:4]}: {vr['c']}件")
                        
                        red_bars.append(r_bar[0])
                        info_dict[len(red_bars)-1] = f"【{d_str}】\n" + "\n".join(txt_lines)

        if red_bars: self.add_hover(ax, cv, red_bars, info_dict)
        
        self._draw_image_links(ax, cv)

    def _get_current_ym_list(self):
        p = self.pcb.get()
        if p == "全期間":
            return sorted(list(getattr(self, 'graph_images', {}).keys()))
        
        sd_val = self.pcd("start")
        ed_val = self.pcd("end")
        if not sd_val: return []
        try:
            sdt = pd.to_datetime(sd_val)
            if p == "月間指定 (1ヶ月)":
                edt = sdt + pd.offsets.MonthEnd(0)
            elif p == "年間指定 (12ヶ月)":
                sdt = sdt.replace(month=1, day=1)
                edt = sdt.replace(month=12, day=31)
            elif p == "週間指定 (7日間)":
                edt = sdt + pd.Timedelta(days=6)
            elif p == "日付指定 (1日)":
                edt = sdt
            else:
                edt = pd.to_datetime(ed_val) if ed_val else sdt
                
            s_m = sdt.replace(day=1)
            e_m = edt.replace(day=1)
            dr = pd.date_range(start=s_m, end=e_m, freq='MS')
            if len(dr) == 0:
                dr = [s_m]
            return [d.strftime("%Y/%m") for d in dr]
        except:
            return []

    def _draw_image_links(self, ax, cv):
        ym_list = self._get_current_ym_list()
        matched_images = []
        if hasattr(self, 'graph_images'):
            for ym in ym_list:
                if ym in self.graph_images:
                    for img_info in self.graph_images[ym]:
                        matched_images.append((ym, img_info))
                        
        # ★凡例と被らないように、下から上に向かって配置する
        y_pos = 0.05 
        
        # 1. 登録ボタン
        txt_reg = ax.text(1.02, y_pos, "➕ 新規画像登録 ", transform=ax.transAxes, 
                      color="#ffffff", fontsize=self.f_size-3, weight="bold", 
                      picker=5, bbox=dict(facecolor='#8e44ad', edgecolor='#8e44ad', boxstyle='round,pad=0.4'))
        txt_reg.is_reg_btn = True
        y_pos += 0.15
        
        # 2. 画像リンク
        for i, (ym, info) in enumerate(matched_images):
            title = info["title"]
            txt = ax.text(1.02, y_pos, f"📸 {title}\n({ym})", transform=ax.transAxes, 
                          color="#0056b3", fontsize=self.f_size-3, weight="bold", 
                          picker=5, bbox=dict(facecolor='#e3f2fd', edgecolor='#0056b3', alpha=0.9, boxstyle='round,pad=0.3'))
            txt.img_info = info
            y_pos += 0.15
            
        if hasattr(self, 'img_pick_cid'):
            cv.mpl_disconnect(self.img_pick_cid)
            
        def on_pick(event):
            if hasattr(event.artist, 'is_reg_btn'):
                self.pop_reg_img()
            elif hasattr(event.artist, 'img_info'):
                self.pop_show_image(event.artist.img_info)
                
        self.img_pick_cid = cv.mpl_connect("pick_event", on_pick)
        
        # ★余白を最適化（0.85から0.93へ変更し、右側の無駄なスペースを削減）
        ax.get_figure().tight_layout(rect=[0, 0, 0.93, 1])
        cv.draw()

    def add_hover(self, ax, cv, bars, info_dict):
        if id(ax) in self.hover_cids: cv.mpl_disconnect(self.hover_cids[id(ax)])
        def hover(event):
            found = False
            if event.inaxes == ax:
                for i, bar in enumerate(bars):
                    cont, _ = bar.contains(event)
                    if cont:
                        txt = info_dict.get(i, "")
                        if txt:
                            x, y = self.root.winfo_pointerx() + 15, self.root.winfo_pointery() + 15
                            self.tooltip.show(x, y, txt); found = True; break
            if not found: self.tooltip.hide()
        self.hover_cids[id(ax)] = cv.mpl_connect("motion_notify_event", hover)

    def save_db(self):
        try: 
            pd.to_pickle({
                "all_data": self.all_data, "bad_delivery_data": self.bad_delivery_data, "depot_map": self.depot_map,
                "my_password": self.my_password, "links": self.links, "elearning_cached_df": self.elearning_cached_df,
                "graph_images": getattr(self, 'graph_images', {}),
                "img_list_geo": getattr(self, 'img_list_geo', "900x600"),
                "ui_state": {'pcb': self.pcb.get(), 'sy': self.sy.get(), 'sm': self.sm.get(), 'sd': self.sd.get(), 'ey': self.ey.get(), 'em': self.em.get(), 'ed': self.ed.get(), 't1_cb': self.t1_cb.get(), 't1_sort': self.t1_sort.get(), 't2_dep': self.t2_dep.get(), 't2_drv': self.t2_drv.get(), 't2_itm': self.t2_itm.get(), 'multi_items_a': getattr(self, 'multi_items_a', []), 'multi_items_b': getattr(self, 'multi_items_b', []), 'multi_drv_list': getattr(self, 'multi_drv_list', []), 'auto_lock_time_str': getattr(self, 'auto_lock_time_str', "5分")}
            }, self.db_path)
        except Exception as e: print(f"Save err: {e}")

    def load_db(self):
        if os.path.exists(self.db_path):
            try:
                st = pd.read_pickle(self.db_path)
                if isinstance(st, dict): 
                    self.all_data = st.get("all_data", {})
                    self.bad_delivery_data = st.get("bad_delivery_data", {})
                    self.depot_map = st.get("depot_map", {})
                    self.my_password = st.get("my_password", None)
                    self.restored_ui_state = st.get("ui_state", {})
                    self.elearning_cached_df = st.get("elearning_cached_df", pd.DataFrame())
                    self.graph_images = st.get("graph_images", {})
                    self.img_list_geo = st.get("img_list_geo", "900x600")
                    if len(st.get("links", [])) == 3: self.links = st.get("links", [])
                for k, df in list(self.all_data.items()):
                    if isinstance(df, pd.DataFrame):
                        for f in self.num_f:
                            if f not in df.columns: df[f] = 0.0
                        for f in self.txt_f:
                            if f not in df.columns: df[f] = ""
                        if "所属デポ" not in df.columns: df["所属デポ"] = df["ドライバー名"].apply(self.get_driver_depot)
            except Exception: self.all_data, self.bad_delivery_data, self.depot_map = {}, {}, {}
            
        self._update_cache()
        if hasattr(self, 'link_labels') and self.link_labels:
            for i in range(3): self.link_labels[i].config(text=f"🔗 {self.links[i]['name']}")
        self.upd_pcb_v()
        self.setup_initial_comboboxes()
        if self.restored_ui_state: self.restore_ui_state()
        if not self.t1_cb.get(): self.t1_cb.set("すべて")
        if not self.t2_dep.get(): self.t2_dep.set("すべて")
        if not self.t2_drv.get(): self.t2_drv.set("全員")
        self.request_upd()

    def restore_ui_state(self):
        if not self.restored_ui_state: return
        pcb_val = self.restored_ui_state.get('pcb')
        if pcb_val: self.pcb.set(pcb_val)
            
        for key, cb in [('sy', self.sy), ('sm', self.sm), ('sd', self.sd), ('ey', self.ey), ('em', self.em), ('ed', self.ed)]:
            val = self.restored_ui_state.get(key)
            if val:
                if val not in cb['values']: cb['values'] = list(cb['values']) + [val]
                cb.set(val)
        self.on_p_change()

        for key, cb in [('t1_cb', self.t1_cb), ('t1_sort', self.t1_sort), ('t2_dep', self.t2_dep), ('t2_drv', self.t2_drv), ('t2_itm', self.t2_itm)]:
            val = self.restored_ui_state.get(key)
            if val:
                if key != 't1_sort' and val not in cb['values']: cb['values'] = list(cb['values']) + [val]
                cb.set(val)
                if key == 't2_dep': self.on_t2_dep()

        self.multi_items_a = self.restored_ui_state.get('multi_items_a', [])
        self.multi_items_b = self.restored_ui_state.get('multi_items_b', [])
        self.multi_drv_list = self.restored_ui_state.get('multi_drv_list', [])
        self.auto_lock_time_str = self.restored_ui_state.get('auto_lock_time_str', "5分")
        self.restored_ui_state = None

    def upd_pcb_v(self):
        ad = self.cached_df["日付"].unique().tolist() if self.cached_df is not None and not self.cached_df.empty and "日付" in self.cached_df.columns else []
        ad = sorted(list(set(ad)))
        for cb in [self.sy, self.ey]: cb["values"] = sorted(list(set([f"{d[:4]}年" for d in ad])))
        for cb in [self.sm, self.em]: cb["values"] = sorted(list(set([f"{d[5:7]}月" for d in ad])))
        for cb in [self.sd, self.ed]: cb["values"] = sorted(list(set([f"{d[8:10]}日" for d in ad])))
        if ad:
            ld, fd = ad[-1], ad[0]
            if not self.sy.get(): self.sy.set(f"{fd[:4]}年"); self.sm.set(f"{fd[5:7]}月"); self.sd.set(f"{fd[8:10]}日")
            if not self.ey.get(): self.ey.set(f"{ld[:4]}年"); self.em.set(f"{ld[5:7]}月"); self.ed.set(f"{ld[8:10]}日")
            
    def rst_db(self, e=None):
        if messagebox.askyesno("初期化", "蓄積されたデータを完全に消去しますか？\n（この操作は元に戻せません）"):
            self.all_data, self.bad_delivery_data, self.depot_map, self.elearning_cached_df, self.graph_images = {}, {}, {}, pd.DataFrame(), {}
            if os.path.exists(self.db_path):
                try: os.remove(self.db_path)
                except: pass
            for cb in [self.sy, self.sm, self.sd, self.ey, self.em, self.ed]: cb.set(""); cb["values"] = []
            self._update_cache(); self.request_upd()
            messagebox.showinfo("初期化完了", "データを完全に初期化しました。")

    def ld_dep(self):
        fs = filedialog.askopenfilenames(title="デポCSV", filetypes=[("CSV", "*.csv")])
        if not fs: return
        for f in fs:
            dn = self.cln_dep(os.path.basename(f).replace(".csv", ""))
            try: df = pd.read_csv(f, encoding='cp932')
            except: df = pd.read_csv(f, encoding='utf-8')
            df = self.cln_cols(df)
            pc = "ドライバー名" if "ドライバー名" in df.columns else (df.columns[0] if len(df.columns) > 0 else None)
            if pc:
                for _, r in df.iterrows():
                    nm = str(r[pc]).strip()
                    if nm and nm != "nan": self.depot_map[nm] = dn
        self.save_db(); self._update_cache(); self.setup_initial_comboboxes(); self.request_upd(); messagebox.showinfo("完了", "同期完了")

    def ld_bad(self):
        fs = filedialog.askopenfilenames(title="不良CSV", filetypes=[("CSV", "*.csv")])
        if not fs: return
        for f in fs:
            fn, df = os.path.basename(f).replace(".csv", ""), None
            for e in ['cp932', 'shift_jis', 'utf-8-sig', 'utf-8']:
                try: 
                    df = pd.read_csv(f, encoding=e, dtype=str)
                    if any(c in df.columns for c in ["配送日", "デポ名", "ドライバ名", "荷主名称", "問合せ中分類"]): break
                except: continue
            if df is not None:
                df.columns = df.columns.str.strip().str.replace("【", "", regex=False).str.replace("】", "", regex=False)
                fdf = df[[c for c in self.b_cols if c in df.columns]].copy()
                for c in self.b_cols:
                    if c not in fdf.columns: fdf[c] = "不適合・空欄"
                self.bad_delivery_data[fn] = fdf[self.b_cols].fillna("").astype(str)
        self.save_db(); self._update_cache(); self.pcb.set("全期間"); self.on_p_change(); self.request_ref_bad(); messagebox.showinfo("完了", "読込完了")

    def ld_csv(self):
        fs = filedialog.askopenfilenames(title="配送CSV", filetypes=[("CSV", "*.csv")])
        if not fs: return
        pw = tk.Toplevel(self.root); pw.geometry("420x140"); pw.configure(bg=CBG); pw.transient(self.root); pw.grab_set()
        lp = tk.Label(pw, text="読込中...", bg=CBG, font=self.fb); lp.pack(pady=10)
        pb = ttk.Progressbar(pw, orient="horizontal", length=340, mode="determinate", maximum=100); pb.pack(pady=5)
        tf, lc = len(fs), 0
        try:
            for idx, f in enumerate(fs):
                fn, df = os.path.basename(f).replace(".csv", ""), None
                for e in ['cp932', 'shift_jis', 'utf-8-sig', 'utf-8']:
                    try: 
                        df = pd.read_csv(f, encoding=e, dtype=str)
                        if any(c in df.columns for c in ["Name", "ドライバー名", "日付", "ｱｽｸﾙ", "SBS"]): break
                    except: continue
                if df is not None:
                    pr = self.proc_csv(df, lp, pb, pw, idx, tf, fn)
                    if pr is not None:
                        if fn in self.all_data: pr = pd.concat([self.all_data[fn], pr], ignore_index=True).drop_duplicates(subset=["日付", "ドライバー名"], keep="last")
                        self.all_data[fn] = pr; lc += 1
            self.save_db(); self._update_cache(); self.upd_pcb_v(); self.pcb.set("全期間"); self.on_p_change(); self.setup_initial_comboboxes(); self.request_upd()
        except Exception as e: messagebox.showerror("エラー", f"読込中にエラーが発生しました。\n{e}")
        finally: pw.destroy()
        if lc > 0: messagebox.showinfo("完了", "読込成功")

    def ld_elearning(self):
        f = filedialog.askopenfilename(title="e-ラーニングCSV読込", filetypes=[("CSV", "*.csv")])
        if not f: return
        df, last_err = None, None
        for e in ['cp932', 'shift_jis', 'utf-8-sig', 'utf-8']:
            try:
                tmp_df = pd.read_csv(f, encoding=e, dtype=str, skiprows=4)
                if not tmp_df.empty: df = tmp_df; break
            except Exception as ex: last_err = ex; continue
            
        if df is not None and not df.empty:
            df.columns = df.columns.str.strip()
            df = df.dropna(how='all')
            df = df.loc[:, ~df.columns.str.contains('^Unnamed')].dropna(axis=1, how='all')
            if len(df.columns) > 2: df = df.iloc[:, :-2]
            if len(df.columns) >= 3:
                cols = list(df.columns); cols[0], cols[2] = cols[2], cols[0]; df = df[cols]
            
            drv_col = next((c for c in df.columns if c in ["ドライバー名", "名前", "氏名", "Name", "ｱｽｸﾙ", "受講者名", "氏名（漢字）"]), None)
            if not drv_col and len(df.columns) > 0: drv_col = df.columns[0]
            
            if drv_col: df = df.rename(columns={drv_col: "ドライバー名"})
            else: df["ドライバー名"] = "不明"
                
            self.elearning_cached_df = df
            self.save_db(); self.upd_tab4(); messagebox.showinfo("完了", "e-ラーニングデータを読み込みました。")
        else:
            messagebox.showerror("エラー", f"CSVの読み込みに失敗しました。\n詳細: {str(last_err) if last_err else 'ファイルが空か、対応していない形式です。'}")

    def ld_elearning_excel(self):
        f = filedialog.askopenfilename(title="e-ラーニングExcel読込", filetypes=[("Excel", "*.xlsb")])
        if not f: return
        try:
            # pyxlsb を使って data シートを読み込む
            df_raw = pd.read_excel(f, sheet_name="data", dtype=str, engine="pyxlsb")
            
            # 必要な列が存在するか確認
            if "学習者名" not in df_raw.columns or "教材名" not in df_raw.columns or "最高状態" not in df_raw.columns:
                messagebox.showerror("エラー", "指定されたファイルまたは『data』シートに必要な列（学習者名、教材名、最高状態）が見つかりません。")
                return

            # 教材名が "-" や NaN の行を除外
            df_raw = df_raw.dropna(subset=["教材名"])
            df_raw = df_raw[df_raw["教材名"] != "-"]

            # 所属デポ列を取得（無い場合は未登録）
            depot_col = "01_LOGISTマスタ.拠点名変換（詳細）"
            if depot_col not in df_raw.columns:
                df_raw[depot_col] = "未登録"
            else:
                # 拠点名に「西湘」が含まれる行のみに絞り込む（西湘運輸以外の他部署データを除外）
                df_raw = df_raw[df_raw[depot_col].astype(str).str.contains("西湘", na=False)]
                
                # 絞り込んだ結果、データが0件になってしまった場合のエラー回避
                if df_raw.empty:
                    messagebox.showwarning("警告", "西湘運輸のデータが見つかりませんでした。\nファイル内容を確認してください。")
                    return

            # 「最高状態」が "済" 以外（未、中断中、未受講など）なら 1 (未達成)、"済" なら 0
            df_raw["未受講"] = df_raw["最高状態"].apply(lambda x: 0 if str(x).strip() == "済" else 1)

            # 横持ちに変換（ピボット）
            df_pivot = df_raw.pivot_table(index=["学習者名", depot_col], columns="教材名", values="未受講", aggfunc='max', fill_value=0).reset_index()
            
            # 列名の整理
            df_pivot = df_pivot.rename(columns={"学習者名": "ドライバー名", depot_col: "所属デポ"})
            
            # Excel上の拠点名（西湘運輸など）を上書きし、アプリに登録してある各ドライバーの所属デポを取得する
            df_pivot["所属デポ"] = df_pivot["ドライバー名"].apply(self.get_driver_depot)

            # ピボット作成時にできる階層インデックス名を削除
            df_pivot.columns.name = None

            self.elearning_cached_df = df_pivot
            self.save_db()
            self.upd_tab4()
            messagebox.showinfo("完了", "e-ラーニングデータ(Excel)を読み込みました。\n未受講・中断中の項目を自動集計しました。")
            
        except Exception as e:
            messagebox.showerror("エラー", f"Excelの読み込みに失敗しました。\n詳細: {e}\n\n※コマンドプロンプトで pip install pyxlsb を実行してライブラリを追加してください。")

    def upd_tab4(self, e=None):
        self.tv_el.delete(*self.tv_el.get_children()); self.a_el.clear(); self.a_el.axis('off'); self.cv_el.draw()
        df = self.elearning_cached_df if hasattr(self, 'elearning_cached_df') else pd.DataFrame()
        if df.empty: return
        
        df_show = df.copy()
        if "所属デポ" not in df_show.columns:
            df_show["所属デポ"] = df_show["ドライバー名"].apply(self.get_driver_depot) if "ドライバー名" in df_show.columns else "未登録"
        
        dps = ["すべて"] + sorted(list(set(df_show["所属デポ"].dropna().astype(str).tolist())))
        c_dep = self.t4_dep.get()
        if c_dep not in dps: dps = list(dps) + [c_dep] if c_dep else dps
        self.t4_dep["values"] = dps
        if not c_dep or c_dep not in dps: c_dep = "すべて"; self.t4_dep.set("すべて")
        if c_dep != "すべて": df_show = df_show[df_show["所属デポ"] == c_dep]
            
        exclude_keywords, exact_exclude = ["ドライバー名", "所属デポ", "営業所", "事業部", "部署"], ["0", "０", "-", "ー", "－", "―", "−"]
        other_cols = [c for c in df_show.columns.tolist() if not any(k in str(c).strip() for k in exclude_keywords) and str(c).strip() not in exact_exclude]
        
        itms = ["すべて(合計)"] + other_cols
        c_itm = self.t4_itm.get()
        if c_itm not in itms: c_itm = "すべて(合計)"
        self.t4_itm["values"] = itms; self.t4_itm.set(c_itm)
        
        for col in other_cols: df_show[col] = pd.to_numeric(df_show[col], errors='coerce').fillna(0)
            
        if c_itm == "すべて(合計)": df_show["表示値"] = df_show[other_cols].sum(axis=1)
        else: df_show["表示値"] = df_show[c_itm]
            
        # ★★★ ここを追加：未達成が0の人は除外する ★★★
        df_show = df_show[df_show["表示値"] > 0]
            
        df_show = df_show.sort_values(by="表示値", ascending=False)
        dynamic_cols = ["ドライバー名", "所属デポ"] + other_cols + ["表示値"]
        self.tv_el["columns"] = dynamic_cols
        
        for c in dynamic_cols:
            if c == "表示値": self.tv_el.heading(c, text="合計" if c_itm == "すべて(合計)" else "選択項目値"); self.tv_el.column(c, width=100, anchor=tk.E)
            elif c == "ドライバー名": self.tv_el.heading(c, text=c); self.tv_el.column(c, width=150, anchor=tk.W)
            elif c == "所属デポ": self.tv_el.heading(c, text=c); self.tv_el.column(c, width=120, anchor=tk.CENTER)
            else: self.tv_el.heading(c, text=c); self.tv_el.column(c, width=120, anchor=tk.E)
        
        for _, r in df_show.iterrows():
            row_data = [r.get("ドライバー名", "不明"), r.get("所属デポ", "未登録")] + [f"{r.get(col, 0):g}" for col in other_cols] + [f"{r.get('表示値', 0):g}"]
            self.tv_el.insert("", tk.END, values=row_data)
            
        if not df_show.empty and df_show["表示値"].sum() > 0:
            self.a_el.axis('on')
            plot_df = df_show.head(40)
            x_pos = range(len(plot_df))
            colors = ["#d62728" if val >= 3 else "#2ca02c" for val in plot_df["表示値"]]
            bars = self.a_el.bar(x_pos, plot_df["表示値"], color=colors, edgecolor=CTXT, linewidth=0.5)
            
            title_text = f"🚨 E-ラーニング 未受講者 🚨" + (f" - {c_dep}" if c_dep != "すべて" else "")
            if c_itm != "すべて(合計)":
                title_text += f" [{c_itm}]"
                
            self.a_el.set_title(title_text, color="#d62728", fontname="MS Gothic", weight='heavy', fontsize=self.f_size + 12, pad=15)
            self.a_el.set_xticks(x_pos); self.a_el.set_xticklabels([str(drv)[:5] for drv in plot_df["ドライバー名"]], rotation=45, ha="right")
            self.a_el.tick_params(labelsize=self.f_size-3)
            
            for b in bars:
                if b.get_height() > 0: self.a_el.annotate(f'{b.get_height():g}', xy=(b.get_x() + b.get_width() / 2, b.get_height()), xytext=(0, 2), textcoords="offset points", ha='center', va='bottom', fontsize=self.f_size - 5, weight='bold')
            
            self.a_el.get_figure().tight_layout(); self.cv_el.draw()
            
            info_dict = {}
            for i, (_, r) in enumerate(plot_df.iterrows()):
                txt_lines = [f"【{r.get('ドライバー名', '不明')}】未達成項目:"]
                count = 0
                for col in other_cols:
                    if r.get(col, 0) > 0: txt_lines.append(f"・{col} : {r.get(col, 0):g}"); count += 1
                if count == 0: txt_lines.append("未達成項目はありません")
                info_dict[i] = "\n".join(txt_lines)

            self.add_hover(self.a_el, self.cv_el, bars, info_dict)
            self.add_el_click_event(self.a_el, self.cv_el, bars, plot_df, other_cols)

    def proc_csv(self, df, lp, pb, pw, fidx, tf, fn):
        try:
            df.columns = df.columns.str.strip().str.replace("【", "", regex=False).str.replace("】", "", regex=False)
            if "備考2" in df.columns and "備考4" in df.columns: df["備考2"] = df["備考2"].fillna("").astype(str) + " " + df["備考4"].fillna("").astype(str); df = df.drop(columns=["備考4"])
            elif "備考4" in df.columns: df["備考2"] = df["備考4"]; df = df.drop(columns=["備考4"])
            df = self.cln_cols(df)
            if "ドライバー名" not in df.columns or "日付" not in df.columns: return None
            
            try: df["_dt"] = pd.to_datetime(df["日付"], errors='coerce', format='mixed')
            except: df["_dt"] = pd.to_datetime(df["日付"], errors='coerce')
                
            df = df.dropna(subset=["_dt", "ドライバー名"]); df["日付"] = df["_dt"].dt.strftime("%Y/%m/%d")
            t_flds = len(self.num_f); bp = (fidx / tf) * 100; pp = 100 / tf
            
            for i, f in enumerate(self.num_f):
                if f != "全体個数" and f in df.columns:
                    try:
                        s = df[f].fillna(0).astype(str).str.replace(",", "", regex=False).str.replace("¥", "", regex=False).str.replace("\\", "", regex=False).str.replace("円", "", regex=False).str.strip()
                        df[f] = pd.to_numeric(s, errors='coerce').fillna(0)
                    except Exception: df[f] = 0.0
                lp.config(text=f"{int(bp + (pp * (i / t_flds)))}% 解析: {f}"); pb['value'] = bp + (pp * (i / t_flds)); pw.update()
                
            for f in self.txt_f: df[f] = df[f].astype(str).replace("nan", "").str.strip() if f in df.columns else ""
            ar = {f: "sum" for f in self.num_f if f != "全体個数" and f in df.columns}
            for f in self.txt_f:
                if f in df.columns: ar[f] = "first"
            dm = df.groupby(["日付", "ドライバー名", "_dt"]).agg(ar).reset_index()
            for f in self.num_f:
                if f not in dm.columns: dm[f] = 0.0
            for f in self.txt_f:
                if f not in dm.columns: dm[f] = ""
            dm["全体個数"] = dm[[f for f in self.num_f if f not in ["全体個数", "チャーター①", "チャーター②", "チャーター③"]]].sum(axis=1)
            dm["所属デポ"] = dm["ドライバー名"].map(lambda d: self.get_driver_depot(d))
            return dm
        except Exception as e: print(f"CSV process error: {e}"); return None

    def on_font_change(self, e=None): pass

    def cln_cols(self, df): return df.rename(columns=RENAME_DIC)

    def add_el_click_event(self, ax, cv, bars, plot_df, other_cols):
        if hasattr(self, 'el_click_cid'): cv.mpl_disconnect(self.el_click_cid)
        def on_click(event):
            if event.inaxes == ax:
                for i, bar in enumerate(bars):
                    if bar.contains(event)[0]:
                        self.tooltip.hide()
                        self.pop_el_delete(plot_df.iloc[i].get("ドライバー名", "不明"), plot_df.iloc[i], other_cols); break
        self.el_click_cid = cv.mpl_connect("button_press_event", on_click)

    def pop_el_delete(self, drv_name, row_data, other_cols):
        p = tk.Toplevel(self.root)
        p.title(f"詳細と完了処理 - {drv_name}")
        p.geometry("600x600")
        p.configure(bg=CBG)
        p.transient(self.root)
        p.grab_set()
        
        tk.Label(p, text=f"👤 {drv_name} の未達成項目", font=self.ft, bg=CBG, fg=CPRI).pack(pady=(10, 5))
        tk.Label(p, text="※完了にしたい項目にチェックを入れ、\n「チェック項目を完了」を押してください。", bg=CBG, font=self.fs, fg="#6c757d").pack(pady=(0, 5))
        
        frame = tk.Frame(p, bg=CCARD, bd=1, relief=tk.SOLID)
        frame.pack(fill=tk.BOTH, expand=True, padx=20, pady=5)
        
        cv = tk.Canvas(frame, bg=CCARD, highlightthickness=0)
        scr = ttk.Scrollbar(frame, orient="vertical", command=cv.yview)
        inner = tk.Frame(cv, bg=CCARD)
        inner.bind("<Configure>", lambda e: cv.configure(scrollregion=cv.bbox("all")))
        cv.create_window((0, 0), window=inner, anchor="nw")
        cv.configure(yscrollcommand=scr.set)
        cv.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5, pady=5)
        scr.pack(side=tk.RIGHT, fill=tk.Y)
        
        count = 0
        check_vars = {}
        
        for col in other_cols:
            val = row_data.get(col, 0)
            if val > 0:
                f_item = tk.Frame(inner, bg=CCARD)
                f_item.pack(fill=tk.X, padx=10, pady=5)
                
                # ★ 修正ポイント1：環境依存バグを回避するため、0か1の数値で判定する方式(IntVar)に変更
                var = tk.IntVar(master=f_item, value=0)
                check_vars[col] = var
                
                tk.Checkbutton(f_item, text=f"{col} (現在: {val:g})", variable=var, onvalue=1, offvalue=0, bg=CCARD, font=self.fn, cursor="hand2").pack(side=tk.LEFT)
                count += 1
                
        if count == 0:
            tk.Label(inner, text="未達成項目がありません。", bg=CCARD, font=self.fn).pack(anchor="w", padx=10, pady=10)
                
        def _apply_checked():
            updated = False
            # ★ 修正ポイント2：ドライバー名が万が一「数字」で保存されていても確実に一致するように文字列(str)に変換して比較
            mask = self.elearning_cached_df["ドライバー名"].astype(str) == str(drv_name)
            
            if mask.any():
                for col, var in check_vars.items():
                    if var.get() == 1:  # チェックが入っている(1になっている)場合
                        self.elearning_cached_df.loc[mask, col] = "0"
                        updated = True
                        
            if updated:
                self.save_db()
                self.upd_tab4()
                p.destroy()
                messagebox.showinfo("更新完了", "選択した項目を完了にしました。")
            else:
                messagebox.showwarning("警告", "チェックされた項目がありません。")

        def _delete():
            if messagebox.askyesno("確認", f"{drv_name} のデータをすべて完了済として削除しますか？\n\n※この操作は元に戻せません。"):
                # ここも同様に安全な比較に変更
                mask = self.elearning_cached_df["ドライバー名"].astype(str) != str(drv_name)
                self.elearning_cached_df = self.elearning_cached_df[mask]
                self.save_db()
                self.upd_tab4()
                p.destroy()
                messagebox.showinfo("削除完了", f"{drv_name} のデータを完了済として処理しました。")
                
        btn_frame = tk.Frame(p, bg=CBG)
        btn_frame.pack(fill=tk.X, padx=20, pady=15)
        
        if count > 0:
            tk.Button(btn_frame, text="☑ チェック項目を完了", bg="#28a745", fg="white", font=self.fb, command=_apply_checked).pack(side=tk.LEFT, expand=True, fill=tk.X, padx=(0, 5))
            
        tk.Button(btn_frame, text="🗑️ すべて完了済として削除", bg="#dc3545", fg="white", font=self.fb, command=_delete).pack(side=tk.LEFT, expand=True, fill=tk.X, padx=(5 if count > 0 else 0, 0))

    def run_sbs_tracking(self):
        raw_val = self.t5_txt.get("1.0", tk.END).strip()
        if not raw_val: return
        
        track_nums = []
        for line in raw_val.split('\n'):
            line = line.strip()
            if not line: continue
            num = re.sub(r'\D', '', line)
            if num:
                track_nums.append(num)
                
        if not track_nums:
            messagebox.showwarning("警告", "有効な伝票番号が見つかりません。")
            return
            
        if len(track_nums) > 100:
            track_nums = track_nums[:100]
            messagebox.showinfo("お知らせ", "100件を超えているため、最初の100件のみを検索します。")
            
        # テキストボックスを抽出後のきれいな数字に置き換え
        self.t5_txt.delete("1.0", tk.END)
        self.t5_txt.insert("1.0", "\n".join(track_nums))
        
        self.t5_btn.config(state=tk.DISABLED)
        total_pages = ((len(track_nums) - 1) // 10) + 1
        self.t5_lbl_status.config(text=f"🔄 検索中... (0/{total_pages} ページ目)", fg=CPRI)
        
        threading.Thread(target=self._fetch_sbs, args=(track_nums,), daemon=True).start()
        
    def _fetch_sbs(self, track_nums):
        if 'webdriver' not in globals() or webdriver is None:
            self.root.after(0, lambda: self._update_sbs_ui("エラー: ブラウザ操作用ライブラリがありません。\nコマンドプロンプトで pip install selenium を実行してください。", None))
            return

        self.is_loading = True
        self.loading_text = "Edgeブラウザを起動しています\n(初回は数秒かかります)..."
        self.loading_idx = 0

        def _animate():
            if getattr(self, "is_loading", False):
                chars = ["●○○", "○●○", "○○●", "○●○"]
                self.t5_lbl_status.config(text=f"{chars[self.loading_idx]} {self.loading_text}", fg=CPRI)
                self.loading_idx = (self.loading_idx + 1) % len(chars)
                self.root.after(200, _animate)

        self.root.after(0, _animate)

        import winreg
        major_version = None
        try:
            key = winreg.OpenKey(winreg.HKEY_CURRENT_USER, r"Software\Microsoft\Edge\BLBeacon")
            version, _ = winreg.QueryValueEx(key, "version")
            major_version = version.split(".")[0]
        except Exception:
            try:
                key = winreg.OpenKey(winreg.HKEY_LOCAL_MACHINE, r"SOFTWARE\WOW6432Node\Microsoft\EdgeUpdate\Clients\{56EB18F8-B008-4CBD-B6D2-8C97FE7E9062}")
                version, _ = winreg.QueryValueEx(key, "pv")
                major_version = version.split(".")[0]
            except Exception:
                pass
                
        if getattr(sys, 'frozen', False):
            base_path = os.path.dirname(sys.executable)
        else:
            base_path = os.path.dirname(os.path.abspath(__file__))
            
        drivers_dir = os.path.join(base_path, "drivers")
        driver_path = None
        
        if major_version:
            expected_driver = os.path.join(drivers_dir, f"msedgedriver_{major_version}.exe")
            if os.path.exists(expected_driver):
                driver_path = expected_driver
                
        if not driver_path:
            fallback_driver = os.path.join(drivers_dir, "msedgedriver.exe")
            if os.path.exists(fallback_driver):
                driver_path = fallback_driver
                
        if not driver_path:
            err_msg = f"エラー: 適切なEdgeドライバーが見つかりません。\n(お使いのPCのEdgeバージョン: {major_version or '不明'})\n\n右上にある「⚠️ エラーが出たらこちら」ボタンを押して、\n手順に従いドライバーを追加してください。"
            self.root.after(0, lambda: self._update_sbs_ui(err_msg, None))
            return

        url = "https://www.saqura-web.com/sbs_ltrc/"
        driver = None
        try:
            options = EdgeOptions()
            options.add_experimental_option("excludeSwitches", ["enable-logging"])
            
            service = EdgeService(executable_path=driver_path)
            driver = webdriver.Edge(service=service, options=options)
            
            all_screenshots = []
            chunks = [track_nums[i:i + 10] for i in range(0, len(track_nums), 10)]
            
            for chunk_idx, chunk in enumerate(chunks):
                self.loading_text = f"検索中... ({chunk_idx+1}/{len(chunks)} ページ目)\n※ブラウザが自動で動きます。触らずにお待ちください。"
                
                driver.get(url)
                time.sleep(1.5)
                
                raw_inputs = driver.find_elements(By.CSS_SELECTOR, "input[type='text']")
                text_inputs = []
                for inp in raw_inputs:
                    if inp.is_displayed() and inp.is_enabled() and not inp.get_attribute("readonly"):
                        text_inputs.append(inp)
                
                for i, num in enumerate(chunk):
                    if i < len(text_inputs):
                        try:
                            text_inputs[i].clear()
                            text_inputs[i].send_keys(num)
                        except:
                            driver.execute_script("arguments[0].value = arguments[1];", text_inputs[i], num)
                        
                search_btn = None
                buttons = driver.find_elements(By.CSS_SELECTOR, "input[type='submit'], input[type='image'], button, input[value*='検索']")
                for btn in buttons:
                    val = btn.get_attribute("value") or ""
                    if "リセット" not in val and "クリア" not in val:
                        search_btn = btn
                        break
                        
                if search_btn:
                    search_btn.click()
                else:
                    forms = driver.find_elements(By.TAG_NAME, "form")
                    if forms:
                        forms[0].submit()
                        
                time.sleep(3.0)
                
                try:
                    body = driver.find_element(By.TAG_NAME, "body")
                    png_data = body.screenshot_as_png
                    all_screenshots.append(png_data)
                except Exception as ex:
                    print(f"Screenshot error: {ex}")
                    pass

            if all_screenshots:
                self.root.after(0, lambda: self._update_sbs_ui(f"✅ 取得完了: {len(track_nums)}件の画像を取得しました", all_screenshots))
            else:
                self.root.after(0, lambda: self._update_sbs_ui("該当データなし、または画像取得エラー。", None))
                
        except Exception as e:
            err_msg = str(e)[:150]
            self.root.after(0, lambda: self._update_sbs_ui(f"エラー発生:\n{err_msg}", None))
        finally:
            if driver is not None:
                try:
                    driver.quit()
                except:
                    pass

    def _update_sbs_ui(self, msg, screenshots):
        # 処理が終わったので、ローディングアニメーションを強制停止させる
        self.is_loading = False 
        
        self.t5_btn.config(state=tk.NORMAL)
        self.t5_lbl_status.config(text=msg, fg=CPRI if "完了" in msg else "#dc3545")
        
        # 印刷・メール機能用に最新のスクショを保存しておく
        self.latest_sbs_screenshots = screenshots
        
        import base64
        
        # 最初の1回目に、Treeviewが置かれている親フレーム（土台）を取得して記憶する
        if not hasattr(self, 't5_display_frame'):
            self.t5_display_frame = self.tv_sbs.master
            
        # 親フレームの中にある古い要素（Treeviewや前回の画像）をすべて白紙にする
        for widget in self.t5_display_frame.winfo_children():
            widget.destroy()
            
        # もし画像が無ければ空のメッセージを置いて終了
        if not screenshots:
            tk.Label(self.t5_display_frame, text="表示できるデータがありません", bg=CCARD, font=self.ft, fg="#6c757d").pack(pady=40)
            return
            
        # 画像表示用のキャンバス（Canvas）とスクロールバーを新しく作成
        self.t5_img_canvas = tk.Canvas(self.t5_display_frame, bg=CCARD)
        self.t5_img_scroll_y = ttk.Scrollbar(self.t5_display_frame, orient=tk.VERTICAL, command=self.t5_img_canvas.yview)
        self.t5_img_scroll_x = ttk.Scrollbar(self.t5_display_frame, orient=tk.HORIZONTAL, command=self.t5_img_canvas.xview)
        self.t5_img_canvas.configure(yscrollcommand=self.t5_img_scroll_y.set, xscrollcommand=self.t5_img_scroll_x.set)
        
        self.t5_img_scroll_x.pack(side=tk.BOTTOM, fill=tk.X)
        self.t5_img_scroll_y.pack(side=tk.RIGHT, fill=tk.Y)
        self.t5_img_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        
        # ガベージコレクション（画像が勝手に消える現象）を防ぐためのリスト
        self.sbs_images = []
        y_offset = 0
        max_w = 0
        
        # スクリーンショットを上から順番に並べて貼り付けていく
        for png_data in screenshots:
            try:
                # バイナリデータをBase64に変換することで、外部ライブラリ無しでTkinterに画像を表示させる
                b64_data = base64.b64encode(png_data).decode('utf-8')
                img = tk.PhotoImage(data=b64_data)
                self.sbs_images.append(img)
                
                # キャンバス上に画像を配置
                self.t5_img_canvas.create_image(0, y_offset, anchor="nw", image=img)
                y_offset += img.height() + 20 # 次の画像との隙間を20px空ける
                
                if img.width() > max_w: 
                    max_w = img.width()
            except Exception as e:
                print(f"Image load error: {e}")
                
        # キャンバスのスクロール範囲を、並べた画像全体のサイズに合わせる
        self.t5_img_canvas.configure(scrollregion=(0, 0, max_w, y_offset))
        
        # --- マウスホイールによるスクロール処理を追加 ---
        def _on_mousewheel(event):
            self.t5_img_canvas.yview_scroll(int(-1 * (event.delta / 120)), "units")
            
        def _bind_mouse(event):
            self.t5_img_canvas.bind_all("<MouseWheel>", _on_mousewheel)
            
        def _unbind_mouse(event):
            self.t5_img_canvas.unbind_all("<MouseWheel>")

        self.t5_img_canvas.bind('<Enter>', _bind_mouse)
        self.t5_img_canvas.bind('<Leave>', _unbind_mouse)

    def upd_sbs_graph(self):
        try:
            self.a6.clear()
            self.a6.axis('off')
            
            if not hasattr(self, 'sbs_data') or self.sbs_data.empty:
                self.a6.text(0.5, 0.5, "データが蓄積されていません", ha='center', va='center', fontsize=self.f_size, color="#6c757d", fontname="MS Gothic", weight="bold")
                self.cv6.draw()
                return

            df = self.sbs_data.copy()
            # ミスミのデータのみを抽出
            df_misumi = df[df["荷主"] == "ミスミ"].copy()
            if df_misumi.empty:
                self.a6.text(0.5, 0.5, "ミスミのデータがありません", ha='center', va='center', fontsize=self.f_size, color="#6c757d", fontname="MS Gothic", weight="bold")
                self.cv6.draw()
                return

            # 配達完了しているもののみを対象
            df_misumi = df_misumi[df_misumi["配達状況"].str.contains("完了", na=False)].copy()
            if df_misumi.empty:
                self.a6.text(0.5, 0.5, "配達完了済のミスミデータがありません", ha='center', va='center', fontsize=self.f_size, color="#6c757d", fontname="MS Gothic", weight="bold")
                self.cv6.draw()
                return
                
            df_misumi["日"] = df_misumi["_dt"].dt.strftime("%m/%d")
            
            # 午前(11:59まで)と午後(12:00以降)を判定
            df_misumi["午前完了"] = df_misumi["_dt"].dt.hour < 12
            
            # 日ごとに集計
            grp = df_misumi.groupby("日")["午前完了"].agg(
                全体個数='count',
                午前個数='sum'
            ).reset_index()
            
            grp["午後・遅れ個数"] = grp["全体個数"] - grp["午前個数"]
            
            # グラフ描画
            self.a6.axis('on')
            x = range(len(grp))
            
            # 積み上げ棒グラフ
            bars_am = self.a6.bar(x, grp["午前個数"], label="午前配達完了", color="#3498db", edgecolor=CTXT, linewidth=0.5)
            bars_pm = self.a6.bar(x, grp["午後・遅れ個数"], bottom=grp["午前個数"], label="午後・遅れ", color="#e74c3c", edgecolor=CTXT, linewidth=0.5)
            
            self.a6.set_title("📊 ミスミ 午前必着達成率", color=CPRI, fontname="MS Gothic", weight='bold', fontsize=self.f_size)
            self.a6.set_xticks(x)
            self.a6.set_xticklabels(grp["日"], rotation=45, ha="right")
            self.a6.tick_params(labelsize=self.f_size-3)
            self.a6.legend(fontsize=self.f_size-4)
            
            # 数値のラベル付け
            for i, row in grp.iterrows():
                total = int(row["全体個数"])
                am = int(row["午前個数"])
                pm = int(row["午後・遅れ個数"])
                if am > 0:
                    self.a6.text(i, am / 2, str(am), ha='center', va='center', color='white', weight='bold', fontsize=self.f_size-4)
                if pm > 0:
                    self.a6.text(i, am + pm / 2, str(pm), ha='center', va='center', color='white', weight='bold', fontsize=self.f_size-4)
                # 全体
                self.a6.text(i, total + (total * 0.02), f"{total}件", ha='center', va='bottom', color='black', weight='bold', fontsize=self.f_size-4)

            self.f6.tight_layout()
            self.cv6.draw()
            
        except Exception as e:
            print(f"Graph update error: {e}")


if __name__ == "__main__":
    try:
        root = tk.Tk()
        app = DataAnalyzerApp(root)
        root.mainloop()
    except Exception as e:
        import traceback
        with open("error_log.txt", "w", encoding="utf-8") as f:
            f.write(traceback.format_exc())
        err = tk.Tk()
        err.withdraw()
        messagebox.showerror("システムエラー", f"起動エラーが発生しました。\nコードの貼り付けミスの可能性があります。\n詳細なエラー内容を『error_log.txt』に保存しました。\n\n【エラー内容】\n{e}")