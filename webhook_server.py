from flask import Flask, request, jsonify
import subprocess

app = Flask(__name__)

@app.route('/push', methods=['POST'])
def receive_push():
    data = request.get_json(silent=True) or {}
    print("📬 Webhook received:", data)
    # run inside the repo so git sees .git and your credential config
    with open("/home/pi/inspections/pdf_job.log", "a") as log:
        subprocess.Popen(
            ["python3", "/home/pi/inspections/process_pdf.py"],
            cwd="/home/pi/inspections",
            stdout=log,
            stderr=log
        )
    return jsonify({"status": "Processing started"}), 200

if __name__ == '__main__':
    app.run(host='0.0.0.0', port=5556)
