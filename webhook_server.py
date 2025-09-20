from flask import Flask, request, jsonify
import subprocess

app = Flask(__name__)

@app.route('/push', methods=['POST'])
def receive_push():
    data = request.get_json()
    print("📬 Webhook received:", data)
    subprocess.Popen(["python3", "/home/pi/inspections/process_pdf.py"])
    return jsonify({"status": "Processing started"}), 200

if __name__ == '__main__':
    app.run(host='0.0.0.0', port=5556)
